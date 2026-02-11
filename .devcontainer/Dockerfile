FROM debian:bookworm
USER root

#region Add basic packages
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get upgrade -y \
    && apt-get install -y --no-install-recommends locales ca-certificates sudo zsh git curl tar \
    && apt-get autoremove -y && apt-get clean -y \
    && echo "en_US.UTF-8 UTF-8" >> /etc/locale.gen && locale-gen \
    && dpkg-reconfigure tzdata
#endregion

#region Set up a new user for development
ARG USERNAME=dev
ARG HOME="/home/${USERNAME}"
RUN useradd -g users -s /bin/zsh -m "${USERNAME}" \
    && usermod -aG sudo ${USERNAME} \
    && echo "${USERNAME} ALL=(root) NOPASSWD:ALL" > /etc/sudoers.d/${USERNAME} \
    && chmod 0440 /etc/sudoers.d/${USERNAME}

USER ${USERNAME}
#endregion

#region Install oh-my-zsh and some plugins
RUN curl -o- https://raw.githubusercontent.com/ohmyzsh/ohmyzsh/master/tools/install.sh | sh \
    && git clone https://github.com/zsh-users/zsh-syntax-highlighting.git ${ZSH_CUSTOM:-~/.oh-my-zsh/custom}/plugins/zsh-syntax-highlighting \
    && git clone https://github.com/zsh-users/zsh-autosuggestions ${ZSH_CUSTOM:-~/.oh-my-zsh/custom}/plugins/zsh-autosuggestions

SHELL [ "/bin/zsh", "-c" ]
RUN source ~/.zshrc \
    && omz theme set ys \
    && omz plugin enable zsh-syntax-highlighting \
    && omz plugin enable zsh-autosuggestions
#endregion

#region Install JDK and set up env
USER ${USERNAME}
ARG JDK_X86_64_DOWNLOAD_URL=https://download.java.net/java/GA/jdk21.0.2/f2283984656d49d69e91c558476027ac/13/GPL/openjdk-21.0.2_linux-x64_bin.tar.gz
ARG JDK_AARCH64_DOWNLOAD_URL=https://download.java.net/java/GA/jdk21.0.2/f2283984656d49d69e91c558476027ac/13/GPL/openjdk-21.0.2_linux-aarch64_bin.tar.gz
RUN mkdir -p ~/apps && cd ~/apps \
    && ARCH=$(uname -m) \
    && if [ "$ARCH" = "x86_64" ]; then \
         JDK_URL=${JDK_X86_64_DOWNLOAD_URL}; \
       elif [ "$ARCH" = "aarch64" ]; then \
         JDK_URL=${JDK_AARCH64_DOWNLOAD_URL}; \
       else \
         echo "Unsupported architecture: $ARCH" && exit 1; \
       fi \
    && curl -O $JDK_URL \
    && tar -zxvf $(basename $JDK_URL) \
    && rm $(basename $JDK_URL) \
    && { \
        echo 'export JAVA_HOME=~/apps/jdk-21.0.2'; \
        echo 'export PATH=$JAVA_HOME/bin:$PATH'; \
    } >> ~/.zshrc \
    && source ~/.zshrc \
    && cat ~/.zshrc \
    && java --version \
    && echo "Java installation completed."

ENV JAVA_HOME=/home/${USERNAME}/apps/jdk-21.0.2
#endregion

#region Install Maven and set up env
USER ${USERNAME}
ARG MAVEN_DOWNLOAD_URL=https://archive.apache.org/dist/maven/maven-3/3.9.9/binaries/apache-maven-3.9.9-bin.tar.gz
RUN mkdir -p ~/apps && cd ~/apps \
    && curl -O ${MAVEN_DOWNLOAD_URL} \
    && tar -zxvf apache-maven-3.9.9-bin.tar.gz \
    && rm apache-maven-3.9.9-bin.tar.gz \
    && { \
        echo 'export M2_HOME=~/apps/apache-maven-3.9.9'; \
        echo 'export PATH=$M2_HOME/bin:$PATH'; \
    } >> ~/.zshrc \
    && source ~/.zshrc \
    && mvn --version \
    && mkdir /home/${USERNAME}/.m2 \
    && chown -R ${USERNAME}:users /home/${USERNAME}/.m2

ENV M2_HOME=/home/${USERNAME}/apps/apache-maven-3.9.9
#endregion

# Switch to dev user
USER ${USERNAME}
WORKDIR /home/${USERNAME}/workspace

ENTRYPOINT [ "/bin/zsh" ]

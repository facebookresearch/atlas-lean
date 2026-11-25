# No codeword is closer than the Hamming decoder's output

Let $D$ be the Hamming (7,4)
decoder and $C \subseteq \mathbb{F}_2^7$ the Hamming code. For every word $y \in \mathbb{F}_2^7$
and every codeword $c \in C$, the Hamming distance between $y$ and $D(y)$ is at most the
Hamming distance between $y$ and $c$.

Since $D(y)$ is itself a codeword, the decoder returns a nearest codeword.

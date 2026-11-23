# The inverse FFT is a normalized FFT at the conjugate root

Let $N = 2^d$, let
$\omega \in \mathbb{C}$ be a primitive $N$-th root of unity and let $x \in \mathbb{C}^N$. The
output of the inverse FFT procedure on $x$ with root $\omega$ is the output of the FFT procedure
on $x$ with root $\overline{\omega}$ with every entry multiplied by $N^{-1}$.

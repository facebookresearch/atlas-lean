# Radix-two fast Fourier transform

For a commutative ring $R$, a natural number $d$, an
element $\omega \in R$ and a vector $x \in R^{2^d}$, the FFT of $x$ with root $\omega$ is defined
by recursion on $d$. For $d = 0$ it returns $x$ at cost $0$. For $d + 1$ it splits $x$ into its
even- and odd-indexed subvectors $e, o \in R^{2^d}$ (cost $4 \cdot 2^d$), computes $\omega^2$
(cost $1$), computes the FFTs $q$ of $e$ and $r$ of $o$ with root $\omega^2$, writes a zero vector
$y \in R^{2^{d+1}}$ (cost $2^{d+1}$), and returns the vector part of the result of the butterfly
pass with $\omega$, $q$ and $r$ on $y$. Its time cost is the sum of the costs of all these steps.

The two transformed halves are stored once and combined with a running twiddle factor. No
assumption on $\omega$ is needed to run the algorithm; one is needed only for its correctness.

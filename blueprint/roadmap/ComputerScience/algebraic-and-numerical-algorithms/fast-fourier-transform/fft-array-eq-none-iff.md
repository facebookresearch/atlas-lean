# The array FFT rejects exactly the non-powers of two

Let $R$ be a commutative ring,
$\omega \in R$ and $x$ an array over $R$. The array FFT of $x$ with root $\omega$ returns no
result if and only if the length of $x$ is different from $2^d$ for every natural number $d$.

In particular the empty array is rejected and an array of length $1 = 2^0$ is accepted.

# The DFT sum at a root of unity depends only on the frequency modulo the length

Let $n$
be a natural number and let $\omega \in \mathbb{C}$ satisfy $\omega^n = 1$. Then for every
$f : \mathbb{N} \to \mathbb{C}$ and every natural number $K$, the discrete Fourier sum of length $n$
at frequency $K$ equals the one at frequency $K \bmod n$:

$$\sum_{j < n} \omega^{jK} f(j) = \sum_{j < n} \omega^{j (K \bmod n)} f(j),$$

where $K \bmod n$ is the remainder of $K$ on division by $n$ (with $K \bmod 0 = K$).

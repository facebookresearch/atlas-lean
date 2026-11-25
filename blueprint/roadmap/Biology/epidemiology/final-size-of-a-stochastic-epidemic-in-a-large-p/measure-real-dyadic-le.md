# For m > 1, a bound on the probability that 2ʲ ≤ F < 2ʲ⁺¹ and F < δN

Let the offspring numbers $\xi_{n,i}$ and the contact targets $U_j$ form a
[final-size epidemic model](is-final-size-epidemic.md) on a probability space $(\Omega, P)$, in the
population $\{0, \dots, N-1\}$, with offspring law $\nu$, a probability measure on $\mathbb{N}$,
with $\int x^2 \, d\nu(x) < \infty$; let $m$ and $\sigma^2$ be its [real mean](offspring-mean.md)
and [real variance](offspring-var.md), and assume $m > 1$. Let $S_0$ be a set of $\#S_0$ initially
susceptible individuals with $p_0 = \frac{N - \#S_0}{N} \le \frac{m - 1}{32\, m}$, let
$j \in \mathbb{N}$ and let $\delta$ be real. The [final size](final-size.md) $F$ satisfies
$P(2^j \le F < 2^{j+1} \text{ and } F < \delta N) \le A_j + B_j + \varepsilon_j$, where
$A_j = 12\, \sigma^2\, 2^{-j} / (m - 1)^2$, $B_j = 256\, m\, p_0\, 2^{-j} / (m - 1)^2$, and
$\varepsilon_j = 64\, m^2\, 2^j / ((m - 1) N)$ if $2^j < \delta N$ and $\varepsilon_j = 0$
otherwise.

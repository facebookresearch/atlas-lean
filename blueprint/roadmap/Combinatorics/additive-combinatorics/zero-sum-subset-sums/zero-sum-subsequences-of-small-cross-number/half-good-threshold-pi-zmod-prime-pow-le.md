# Threshold version of Geroldinger's theorem

Let $d \ge 0$, let $p_1, \dots, p_d$ be
primes, not necessarily distinct, and for each $k$ let
$\Gamma_k = \prod_{i=1}^d \mathbb{Z}/p_i^k\mathbb{Z}$, and let $P_{1/2}(\Gamma_k)$ be its
half-good threshold. Write $\lg = \log_2$. Then there is a real constant $C$ such that for all
sufficiently large $k$,

$$
P_{1/2}(\Gamma_k) \le k^d \exp\left(\left(\frac{(d+1)! \prod_{i=1}^d \lg p_i}{2}
\lg k\right)^{1/(d+1)} - \frac{d}{d+1} \lg \lg k + C\right).
$$

This is an upper bound only, as in the journal record (the source's final comments say the bound
need not be an equality). The case $d = 0$, where $\Gamma_k$ is trivial, is included.

## Sources

- Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in Abelian Groups*, INTEGERS 24 (2024), Article A93, Theorem 4 (`integers-2024-A93-thm-4`).

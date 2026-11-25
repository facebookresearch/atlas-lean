# Summable deviation probabilities along the quadratic subsequence

Let $\mu$ be a
probability measure on $\Omega$, let $A_0, A_1, \dots$ be pairwise independent measurable
subsets of $\Omega$, write $S_n = \sum_{i < n} 1_{A_i}$, and suppose that
$\mathbb{E}[S_n] = \int S_n \, d\mu \to \infty$ as $n \to \infty$. Let $\varphi(k)$ be the least
$n$ with $\mathbb{E}[S_n] \ge (k+1)^2$. Then for every real $\varepsilon > 0$, the sum over
$k \in \mathbb{N}$ of the probabilities
$\mu\{\omega : |S_{\varphi(k)}(\omega) / \mathbb{E}[S_{\varphi(k)}] - 1| \ge \varepsilon\}$
is finite.

By Chebyshev's inequality the $k$-th term is at most $1/(\varepsilon^2 (k+1)^2)$; this is the
Borel–Cantelli input along the subsequence.

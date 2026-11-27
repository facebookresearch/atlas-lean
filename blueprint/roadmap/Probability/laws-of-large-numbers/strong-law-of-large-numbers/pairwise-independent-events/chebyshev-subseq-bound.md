# Chebyshev bound along the subsequence

Let $\mu$ be a probability measure on $\Omega$, let
$A_0, A_1, \dots \subseteq \Omega$ be pairwise independent measurable sets, let
$S_n = \sum_{i\lt n} 1_{A_i}$, and suppose that $\mathbb{E}[S_n] \to \infty$. For $k \in \mathbb{N}$
let $\varphi(k)$ be the least $n$ with $\mathbb{E}[S_n] \ge (k+1)^2$. Then for every
$\varepsilon > 0$ and every $k \in \mathbb{N}$, the probability of the set of $\omega$ with
$|S_{\varphi(k)}(\omega)/\mathbb{E}[S_{\varphi(k)}] - 1| \ge \varepsilon$ is at most
$1/(\varepsilon^2 (k+1)^2)$.

These bounds are summable in $k$, which gives almost sure convergence along the subsequence.

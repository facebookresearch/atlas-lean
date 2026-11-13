# Dirichlet series of the coprimality indicator

Let $k \ge 2$, let $E$ be a set of pairs
$(a, b)$ with $1 \le a < b \le k$, let $G$ be the graph on $\{1, \dots, k\}$ with edge set $E$, and
let $J$ be a vertex cover of $G$, that is, every edge of $E$ has an endpoint in $J$. Let
$\delta_G(n_1, \dots, n_k)$ be $1$ if $\gcd(n_a, n_b) = 1$ for every $(a, b) \in E$, and $0$
otherwise. For $L \subseteq J$ let $N(L)$ be the set of vertices adjacent to some vertex of $L$.
Then for all complex numbers $s_1, \dots, s_k$ with $\operatorname{Re} s_i > 1$ for every $i$,

$$\sum_{n_1, \dots, n_k \ge 1} \frac{\delta_G(n_1, \dots, n_k)}{n_1^{s_1} \cdots n_k^{s_k}} =
\zeta(s_1) \cdots \zeta(s_k) \prod_p \sum_{L} \prod_{\ell \in L} p^{-s_\ell}
\prod_{i \in (J \setminus L) \cup (N(L) \setminus J)} \left(1 - p^{-s_i}\right),$$

where $\zeta$ is the Riemann zeta function, the product runs over all primes $p$, and the sum over
all independent sets $L \subseteq J$ of $G$, that is, subsets of $J$ such that no edge of $E$ has
both endpoints in $L$.

## Sources

- László Tóth, *On the Asymptotic Density of k-tuples of Positive Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27 (2024), Article 24.8.5, Theorem 7 (`jis-2024-24.8.5-thm-7`).

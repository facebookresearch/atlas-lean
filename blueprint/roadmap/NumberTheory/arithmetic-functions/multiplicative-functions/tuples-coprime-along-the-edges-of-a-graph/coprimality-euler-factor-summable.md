# Absolute convergence of the vertex-cover Euler product

Let $k \ge 2$, let $E$ be a set of
pairs $(a, b)$ with $1 \le a < b \le k$, let $G$ be the graph on $\{1, \dots, k\}$ with edge set
$E$, and let $J$ be a vertex cover of $G$, that is, every edge of $E$ has an endpoint in $J$. For
$L \subseteq J$ let $N(L)$ be the set of vertices adjacent to some vertex of $L$. For complex
numbers $s = (s_1, \dots, s_k)$ and a prime $p$ put

$$D'_{G,p}(s) = \sum_{L} \prod_{\ell \in L} p^{-s_\ell}
\prod_{i \in (J \setminus L) \cup (N(L) \setminus J)} \left(1 - p^{-s_i}\right),$$

the sum running over all independent sets $L \subseteq J$ of $G$, that is, subsets of $J$ such that
no edge of $E$ has both endpoints in $L$. Suppose that $\operatorname{Re} \sum_{i \in T} s_i > 1$
for every set $T$ of at least two vertices each of which lies on some edge of $E$. Then
$\sum_p |D'_{G,p}(s) - 1| < \infty$, the sum running over all primes $p$.

## Sources

- László Tóth, *On the Asymptotic Density of k-tuples of Positive Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27 (2024), Article 24.8.5, Theorem 7 (`jis-2024-24.8.5-thm-7`).

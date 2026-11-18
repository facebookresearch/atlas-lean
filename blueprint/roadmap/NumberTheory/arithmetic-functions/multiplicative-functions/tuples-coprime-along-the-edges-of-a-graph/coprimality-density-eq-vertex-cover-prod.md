# Vertex-cover Euler product for the coprimality density

Let $k \ge 2$, let $E$ be a set of
pairs $(a, b)$ with $1 \le a < b \le k$, let $G$ be the graph on $\{1, \dots, k\}$ with edge set
$E$, and let $A_G$ be its coprimality density. Let $J \subseteq \{1, \dots, k\}$ be a vertex cover
of $G$, that is, every edge of $E$ has an endpoint in $J$. For $L \subseteq J$ let $N(L)$ be the
set of vertices adjacent to some vertex of $L$. Then

$$A_G = \prod_p \sum_{L} \left(\frac{1}{p}\right)^{|L|}
\left(1 - \frac{1}{p}\right)^{|J \setminus L| + |N(L) \setminus J|},$$

where the product runs over all primes $p$ and the sum over all independent sets $L \subseteq J$
of $G$, that is, subsets of $J$ such that no edge of $E$ has both endpoints in $L$.

## Sources

- László Tóth, *On the Asymptotic Density of k-tuples of Positive Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27 (2024), Article 24.8.5, Theorem 9 (`jis-2024-24.8.5-thm-9`).

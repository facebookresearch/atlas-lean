# Distortion of a metric embedding and the Euclidean dimension-reduction function

Let $(X, d_X)$ and $(Y, d_Y)$ be metric spaces. An injective map $f : X \to Y$ has *distortion* at most $D \ge 1$ if there is a scale $r > 0$ such that

$$
r\, d_X(x, y) \le d_Y(f(x), f(y)) \le D\, r\, d_X(x, y) \quad \text{for all } x, y \in X,
$$

and $c_Y(X)$ denotes the infimum of the distortions of maps $X \to Y$. For a finite $X \subset \mathbb{R}^d$ with $|X| = n$ and $0 < \varepsilon < 1$, let $m(X, \varepsilon)$ be the least $m$ for which some map $f : X \to \mathbb{R}^m$ satisfies

$$
(1 - \varepsilon)\|x - y\|_2^2 \le \|f(x) - f(y)\|_2^2 \le (1 + \varepsilon)\|x - y\|_2^2 \quad \text{for all } x, y \in X,
$$

and $m(n, d, \varepsilon) = \max\{m(X, \varepsilon) : X \subset \mathbb{R}^d, |X| = n\}$.

## Sources

- William B. Johnson, Joram Lindenstrauss, "Extensions of Lipschitz mappings into a Hilbert space", Contemp. Math. 26 (1984).
- Kasper Green Larsen, Jelani Nelson, "Optimality of the Johnson-Lindenstrauss Lemma", FOCS (2017), arXiv:1609.02094.
- Nathan Linial, Eran London, Yuri Rabinovich, "The geometry of graphs and some of its algorithmic applications", Combinatorica 15 (1995).

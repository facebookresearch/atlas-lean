# Erdős problem 991: cap discrepancy of Fekete points

This result proves the proposition stated as [Statement of Erdős problem 991: cap discrepancy of Fekete points](fekete-points-cap-discrepancy-small.md). Precisely, for every $\varepsilon > 0$ there is $N$ such that for every $n \ge N$ and every set $A \subset S^2$ of exactly $n$ points maximizing the product $\prod_{i<j} \lVert w_i - w_j \rVert$ among all $n$-point subsets of the unit sphere $S^2 \subset \mathbb{R}^3$, every spherical cap $C$ satisfies

$$\bigl\lvert\, \#(A \cap C) - \alpha_C\, n \,\bigr\rvert \le \varepsilon n.$$

Here a spherical cap is a set $C = \{\, x \in S^2 : \langle x, v \rangle \ge t \,\}$ with pole $v \in S^2$ and $t \in \mathbb{R}$, and $\alpha_C$ is the surface measure of $C$ normalized so that the whole sphere has measure $1$. That is, $\max_C \lvert \#(A \cap C) - \alpha_C n \rvert = o(n)$ for maximizers $A$.

## Sources

- T. F. Bloom, Erdős Problems, Problem #991. https://www.erdosproblems.com/991
- J. S. Brauchart, Optimal logarithmic energy points on the unit sphere, Math. Comp. (2008), 1599–1613.

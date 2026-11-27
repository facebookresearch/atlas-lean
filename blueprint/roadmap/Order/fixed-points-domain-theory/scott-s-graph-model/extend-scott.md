# Scott's extension of a map into `P(ω)`

For a subset $X$ of a topological space $Y$ and any map $f : X \to P(\omega)$, Scott's extension $\bar f : Y \to P(\omega)$ is

$$\bar f(y) = \bigcup \Big\{ \bigcap \{ f(x) \mid x \in X \cap U \} \Bigm| U \text{ open},\ y \in U \Big\},$$

with the empty intersection equal to $\mathbb{N}$ (D. Scott, *Data types as lattices*, SIAM J. Comput. 5(3) (1976), Theorem 1.5, the formula for the extension). Equivalently, $m \in \bar f(y)$ if and only if some open $U \ni y$ has $m \in f(x)$ for all $x \in X \cap U$.

## Background

- [Scott's extension is continuous](continuous-extend-scott.md) and [Scott's extension extends a continuous map](extend-scott-apply.md): its two properties.

## Sources

- D. Scott, *Data types as lattices*, SIAM Journal on Computing 5(3) (1976), 522–587, doi:10.1137/0205037.

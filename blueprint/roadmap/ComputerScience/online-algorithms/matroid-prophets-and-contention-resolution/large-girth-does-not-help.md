# Large girth does not improve matroid prophet ratios

For every $k \ge 1$ and every $\varepsilon > 0$ there are a graphic matroid of girth at least $k$ (every circuit has at least $k$ elements) and a prophet inequality instance on it that admits no online policy with competitive ratio at least $\frac12 + \varepsilon$. Hence, unlike for uniform matroids, forbidding small circuits does not allow ratios approaching $1$.

## Proof sketch

Alon, Gravin, Pollner, Rubinstein, Wang, Weinberg and Zhang start from a dense graph on $n$ vertices with girth at least $k$ and at least $n \log n$ edges, subdivide every edge into two edges through a new vertex, and place a copy of the two-value single-item prophet instance on each pair; any online policy can complete at most $n - 1$ pairs without closing a cycle, leaving most remaining pairs blocked as $n$ grows.

## Depends on

- [Matroid prophet inequality](matroid-prophet-problem.md)

## Proof depends on

- [Kleinberg–Weinberg: every matroid admits a $1/2$ prophet inequality](matroid-prophet-half.md)

## Sources

- Noga Alon, Nick Gravin, Tristan Pollner, Aviad Rubinstein, Hongao Wang, S. Matthew Weinberg, Qianfan Zhang, "A Bicriterion Concentration Inequality and Prophet Inequalities for k-Fold Matroid Unions", ITCS (2025), arXiv:2411.11741, Theorem 1.

# The k-DS dimension characterizes k-list learnability

For every $k \ge 1$ and every nonempty $H \subseteq Y^X$ (the $k$-DS dimension is defined only for nonempty classes), $H$ is $k$-list PAC learnable if and only if its $k$-DS dimension is finite. When $d_{k\text{-DS}}(H) = d < \infty$, the realizable sample complexity is polynomial in $d$, $k$, $1/\varepsilon$ and $\log(1/\delta)$ up to logarithmic factors.

## Proof sketch

Necessity: a $k$-pseudo-cube of dimension $d$ forces every $k$-list orientation of its one-inclusion hypergraph to miss the label on a constant fraction of coordinates, giving a lower bound of order $d$ on the sample size. Sufficiency generalizes the multiclass proof: $k$-list analogues of the out-degree lemma yield list learners with large menus and constant success, which are boosted and compressed into $k$-list predictors with small error.

## Depends on

- [k-pseudo-cubes and the k-DS dimension](k-pseudo-cube.md)
- [List PAC learners and list learnability](list-pac-learner.md)

## Proof depends on

- [Quantitative multiclass PAC bounds from the DS dimension](ds-dimension-sample-complexity.md)

## Sources

- M. Charikar, C. Pabbaraju, "A Characterization of List Learnability", STOC (2023), arXiv:2211.04956, Definitions 2 and 4, Theorems 1 and 2.

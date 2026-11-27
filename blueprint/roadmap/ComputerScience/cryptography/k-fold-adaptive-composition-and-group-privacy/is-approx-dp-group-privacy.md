# Group privacy for approximate differential privacy

Let $M$ be [$(\varepsilon, \delta)$-differentially private](../approximate-differential-privacy/is-approx-dp.md) for [replace-one adjacency](../differential-privacy/replace-one.md) on databases $\mathrm{Fin}\,n \to X$. If $d$ and $d'$ are joined by a [replace-one chain](replace-one-chain.md) of length $k$, then for every set $S$ of outputs,

$$
M(d)(S) \le e^{k\varepsilon}\, M(d')(S) + \delta \sum_{j < k} e^{j\varepsilon} .
$$

The error term is the finite sum itself, so the case $\varepsilon = 0$ gives $k\delta$.

# Coalescence along one branch of the species tree

Let $t$ be a real number, $m$ a natural number, $b$ a list of lineages (sets of sampled genes), $A$ a set of clusters and $k$ a real function of a number of lineages, a list of lineages and a set of clusters. The branch step is

$$\sum_{j=1}^{m} q_{mj}(t) \int k\bigl(j,\ b_{m-j}(h),\ A \cup C_{m-j}(h)\bigr)\, \rho_m(dh),$$

where $q_{mj}(t)$ is [Tavaré's probability](../ancestral-lineage-counting-and-tavar-s-formula/tavare-prob.md), $\rho_m$ is the random-joining law on ranked histories of $m$ lineages (the uniform choice of the merging pair at each step), $b_{m-j}(h)$ is the [list of lineages after the first $m - j$ events](merge-along.md) of $h$ started from $b$, and $C_{m-j}(h)$ is the set of [clusters formed along](clades-along.md) these events. For $t \ge 0$, it describes one population along a branch of length $t$ that receives the $m$ lineages $b$ and the clusters $A$ formed below it: the number $j$ of lineages left at the top of the branch has Tavaré's law, and, independently of the coalescence times, the order of the $m - j$ coalescences is the beginning of a random-joining history; the continuation $k$ receives the number of exiting lineages, the lineages and the clusters formed so far.

# Block counts by size weighted by $T_k$ sum to $\sum_k k\,T_k$

Let $n$ be a natural number, $\mathbf{p} = (p_0, p_1, \dots)$ a list of block-size lists and $T_k$
($k \in \mathbb{N}$) real numbers. Suppose that for every $k$ with $2 \le k \le n$ the list
$p_{n-k}$ has exactly $k$ entries, each at least $1$, whose sum is $n$, where $p_{n-k}$ is the
empty list when $\mathbf{p}$ has no entry of index $n - k$. Then

$$\sum_{i=1}^{n-1} \sum_{k=2}^{n} c_i(p_{n-k})\, T_k = \sum_{k=2}^{n} k\, T_k,$$

where $c_i(p)$ is the number of entries of the list $p$ equal to $i$. The weights $T_k$ are
arbitrary real numbers, of any sign. When they are the holding times of a genealogy, the inner
sums are the [total branch lengths subtending $i$ sample copies](sfs-length.md) $L_i$ and the
right side is the
[total branch length](../kingman-s-coalescent-and-watterson-s-estimator/total-length.md) $L$:
pathwise, $\sum_{i=1}^{n-1} L_i = L$. The hypothesis
holds for every history that random joining started from $n$ singletons visits with positive
probability, which gives the [almost-sure version](sum-sfs-length-ae-eq-total-length.md).

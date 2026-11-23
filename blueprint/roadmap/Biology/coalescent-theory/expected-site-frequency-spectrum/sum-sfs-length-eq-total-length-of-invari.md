# Frequency-class branch lengths sum to the total branch length

Let $(T_k)$ be [Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)
of a sample of size $n$ under a measure $\mu$ on $\Omega$, let $\omega \in \Omega$, and let
$\mathbf{p} = (p_0, p_1, \dots)$ be a list of block-size lists such that, for every $k$ with
$2 \le k \le n$, the list $p_{n-k}$ (the empty list if $\mathbf{p}$ has no entry of index $n - k$)
has exactly $k$ entries, each at least $1$, whose sum is $n$. Then

$$\sum_{i=1}^{n-1} L_i(\omega) = L(\omega),$$

where $L_i(\omega)$ is the [total branch length subtending $i$ sample copies](sfs-length.md)
computed from $\mathbf{p}$ and the holding times $T_k(\omega)$, and
$L(\omega) = \sum_{k=2}^{n} k\, T_k(\omega)$ is the
[total branch length](../kingman-s-coalescent-and-watterson-s-estimator/total-length.md). This is
the case $T_k = T_k(\omega)$ of the [identity for arbitrary real weights](sum-sum-count-mul-eq-sum-mul.md).

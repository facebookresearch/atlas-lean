# Almost surely the frequency-class lengths sum to the total length

Let $\mu$ be a probability measure on a measurable space $\Omega$, $n$ a natural number, $(T_k)$
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size $n$ under $\mu$, and $\tau$ a map from $\Omega$ to lists of block-size lists with
the [random-joining law](random-joining.md) started from $n$ singletons:

$$\mu(\tau = \mathbf{p}) = R_{n-1}\bigl((1, \dots, 1), \mathbf{p}\bigr) \quad \text{for every }
\mathbf{p},$$

where $(1, \dots, 1)$ is the list of $n$ ones and $n - 1$ is natural subtraction: for $n = 0$
the initial list is empty, no step is taken, and the law is concentrated on the history whose
only entry is the empty list. Neither the measurability of $\tau$ nor its independence from the
holding times is assumed (the measure of a non-measurable set is read as its outer measure).
Then for $\mu$-almost every $\omega$,

$$\sum_{i=1}^{n-1} L_i(\omega) = L(\omega),$$

where $L_i(\omega)$ is the [total branch length subtending $i$ sample copies](sfs-length.md)
computed from $\tau(\omega)$ and the holding times $T_k(\omega)$, and
$L = \sum_{k=2}^{n} k\, T_k$ is the
[total branch length](../kingman-s-coalescent-and-watterson-s-estimator/total-length.md). For
$n \le 1$ both sums have no terms and the identity reads $0 = 0$.

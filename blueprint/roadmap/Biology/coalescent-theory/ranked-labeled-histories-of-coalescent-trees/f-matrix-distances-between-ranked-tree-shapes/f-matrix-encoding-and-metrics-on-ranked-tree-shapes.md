# F-matrix encoding and metrics on ranked tree shapes

**Ranked tree shapes.** A ranked tree shape $T^R$ with $n$ leaves is a rooted binary unlabeled tree together with a total order of its $n-1$ internal (coalescence) nodes in time. For isochronous sampling at time $u_n = 0$, let $u_{n-1} < \dots < u_1$ be the coalescence times, with time increasing towards the root.

**F matrix.** The F matrix of $T^R$ is the $(n-1)\times(n-1)$ lower-triangular integer matrix with $F_{i,j} = 0$ for $i < j$ and, for $1 \le j \le i$,

$$F_{i,j} = \#\{\text{lineages extant in } (u_{j+1}, u_j) \text{ that do not bifurcate anywhere in } (u_{i+1}, u_j)\}.$$

In particular $F_{i,i} = i+1$, the number of lineages in the $i$-th interval. With $m$ distinct sampling times (heterochronous sampling) the same construction over all $n + m - 2$ change points gives an $(n+m-2)\times(n+m-2)$ matrix.

**Theorem (unique encoding).** The map sending a ranked tree shape with $n$ samples and $m$ sampling events to its F matrix is injective: an F matrix that encodes a ranked tree shape encodes exactly one.

**Metrics.** For ranked tree shapes with F matrices $F^{(1)}, F^{(2)}$ of size $r \times r$,

$$d_1(T_1^R, T_2^R) = \sum_{i=1}^r \sum_{j=1}^i \big|F^{(1)}_{i,j} - F^{(2)}_{i,j}\big|, \qquad d_2(T_1^R, T_2^R) = \Big(\sum_{i=1}^r \sum_{j=1}^i \big(F^{(1)}_{i,j} - F^{(2)}_{i,j}\big)^2\Big)^{1/2}.$$

For ranked genealogies $g^R$ (with branch lengths), the weight matrix $W_{i,j} = u_j - u_{i+1}$ for $j \le i$ (and $0$ otherwise) records the duration of the time span from change point $i+1$ to $j$, and the weighted distances $d_1^w, d_2^w$ replace $F_{i,j}$ by $F_{i,j}W_{i,j}$. All four are metrics.

**Summary statistics.** For a sample $\{T_1^R, \dots, T_s^R\}$, the $L_2$-medoid set is $\arg\min_{T \in \{T_k^R\}} \sum_k d_i(T, T_k^R)^2$, used as a measure of center, with the corresponding mean squared distance as a measure of dispersion.

## Depends on

- [Ranked labeled history](../ranked-history.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

Reading the columns left to right records, for each interval, how the lineages present then are progressively consumed by later (tipward) branchings; since each coalescence removes exactly one lineage from the set of non-bifurcating lineages in one column, the tree shape and its ranking can be rebuilt interval by interval from the matrix, which gives injectivity. The distances are then the element-wise $L_1$ and $L_2$ norms pulled back through an injective map, so the metric axioms are inherited. Because the encoding ignores labels and keeps only the time order of coalescences, it is suited to comparing genealogies of exchangeable samples, for instance posterior samples of coalescent genealogies or trees from different demographic models, and the weighted version adds sensitivity to coalescence times.

## Sources

- J. Kim, N. A. Rosenberg, J. A. Palacios, "Distance metrics for ranked evolutionary trees", Proceedings of the National Academy of Sciences USA 117(46):28876–28886 (2020), Theorem 1, Eqs 1–5, Proposition 2, <https://doi.org/10.1073/pnas.1922851117>, PMCID PMC7682335.

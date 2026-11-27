# Invisible transitions of the SMC$'$ and the $F$ matrix

A recombination event in the SMC$'$ is **invisible** when the detached branch coalesces back onto the same lineage it was pruned from, so that the new local genealogy equals the old one. Fix a local genealogy $g$ of $n$ sequences with coalescence times $t_n < \dots < t_2$ and $t_{n+1} = 0$, and let $A(t)$ be its number of ancestral lineages at time $t$. For $n \ge j \ge k \ge 2$ define $F_{j,k}$ as the number of lineages of $g$ that are free — that is, that do not coalesce — throughout the time interval $(t_{j+1}, t_k)$. Define also

$$Q_j = \int_{t_{j+1}}^{t_j} \exp\left\{-\int_{u}^{t_j} \frac{A(r)}{N(r)}dr\right\} du, \qquad q_l = \exp\left\{-\int_{t_{l+1}}^{t_l} \frac{A(r)}{N(r)} dr \right\},$$

and set

$$P_{j,j} = \frac{1}{j} \int_{t_{j+1}}^{t_j} \left(1 - \exp\left\{-\int_{u}^{t_j} \frac{A(r)}{N(r)}\,dr\right\}\right) du, \qquad P_{j,k} = Q_j\, q_{j-1} q_{j-2} \cdots q_{k+1} \frac{1 - q_k}{k} \quad (k < j),$$

so that $P_{j,k}/\ell$ is the probability that a fixed lineage free on $(t_{j+1}, t_k)$ is pruned in $(t_{j+1}, t_j)$ and regrafts back onto itself in $(t_{k+1}, t_k)$ (among the $k$ lineages present there). Then the marginal probability of an invisible transition is

$$\Pr[G_i = g \mid g, N(t)] = \frac{1}{\ell} \sum_{j=2}^{n} \sum_{k=2}^{j} F_{j,k}\, P_{j,k},$$

with $\ell$ the total length of $g$. The numbers $F_{j,k}$ form a lower-triangular matrix, the $F$ matrix of the genealogy, and $F$ matrices are in bijection with ranked tree shapes.

## Depends on

- [Marginal visible transition density under the SMC$'$](marginal-visible-transition-density-under-the-smc-prime.md)
- [Probability of a ranked tree shape under the coalescent](../../ranked-labeled-histories-of-coalescent-trees/tajima-genealogies/probability-of-a-ranked-tree-shape.md)

## Expansion

The double sum decomposes an invisible event by the coalescent interval containing the pruning time and the coalescent interval containing the regrafting time. For $k < j$, given a pruning time in $(t_{j+1}, t_j)$, the detached branch must avoid coalescing until it reaches the target interval, which contributes $Q_j$ and the intermediate survival factors $q_l$; it then coalesces in $(t_{k+1}, t_k)$ with probability $1 - q_k$, and lands back on the pruned lineage, one of the $k$ lineages present there, with probability $1/k$, giving $(1 - q_k)/k$. For $k = j$ pruning and regrafting fall in the same interval, so the pruning time $u$ and the regrafting time are integrated together, which gives the integral $P_{j,j}$ with its factor $1/j$. In both cases the pruned lineage must be one of the $F_{j,k}$ lineages that are free over the whole span, since only those can receive the detached branch back. The factor $1/\ell$ is the uniform density of the pruning location. Because the transition probabilities depend on the labelled topology only through the counts $F_{j,k}$, the labels of the tips carry no information about $N(t)$ beyond the ranked tree shape, which is the combinatorial content of the bijection and the reason the state space for inference can be reduced from labelled genealogies to ranked ones.

## Sources

- J. A. Palacios, J. Wakeley, S. Ramachandran, "Bayesian nonparametric inference of population size changes from sequential genealogies", *Genetics* 201 (2015), 281–304, <https://doi.org/10.1534/genetics.115.177980> (PMC4566269). Methods: SMC$'$ calculations, Equations (9)–(11), and Appendix.

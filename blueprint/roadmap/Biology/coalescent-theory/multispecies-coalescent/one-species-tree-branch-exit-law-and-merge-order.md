# One species-tree branch: exit law and merge order of the realized coalescent

Run $m \ge 1$ lineages of Kingman's coalescent, realized as a continuous-time Markov chain path, along a branch of length $t \ge 0$. Then the number $J$ of lineages leaving the top of the branch has the law given by [Tavaré's formula](../ancestral-lineage-counting-and-tavar-s-formula/tavare-prob.md),

$$\mathbb{P}(J = j) = g_{mj}(t), \qquad 1 \le j \le m,$$

and conditionally on $J = j$ the order in which the lineages merged is random joining, independent of the merger times.

## Depends on

- [Tavaré's formula for the number of ancestral lineages](../ancestral-lineage-counting-and-tavar-s-formula/tavare-prob.md)
- [Holding times and jump chain of Kingman's n-coalescent are independent](../partition-valued-kingman-coalescent/holding-times-and-jump-chain-of-kingman-s-n-coal.md)

## Proof depends on

- [Finite-dimensional distributions](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-input-measure-real-ctmc-path-fdd.md)

## Expansion

1. The exit law from the finite-dimensional distributions of the block-counting chain.
2. The merge order from the independence of the jump chain and the holding times.
3. Checks: the law matches the branch step of the gene tree probability of [the multispecies coalescent](gene-tree-prob.md), and $t = 0$ gives $J = m$.

## Sources

- J. H. Degnan and L. A. Salter, Gene tree distributions under the coalescent process, *Evolution* 59 (2005), 24–37 (gene tree distributions).

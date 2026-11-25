# Path probability of the Kingman coalescent jump chain

For a natural number $n$ and a finite list $(\pi_0, \dots, \pi_r)$ of partitions in $\mathcal{P}_n$, its path probability is $0$ for the empty list, and otherwise

$$[\pi_0 = \bot] \prod_{i=0}^{r-1} J_n(\pi_i, \pi_{i+1}),$$

where $J_n$ is the [jump matrix](jump-matrix.md): the probability that the jump chain of Kingman's $n$-coalescent, started from the partition into singletons, follows the list.

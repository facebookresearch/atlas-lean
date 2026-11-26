# Waiting distance until the next tree change under the SMC'

Let $\mathcal{T}$ be the local coalescent tree at a position of the genome, with total branch length
$L(\mathcal{T})$ in coalescent units of $2N_e$ generations, and let $\rho/2 = 2N_e r$ be the
population-scaled recombination rate per base pair. Under the sequentially Markovian coalescent SMC', the
distance $d$ along the genome to the next change of the tree, that is to the next change of at least one
coalescence time, has density

$$p_r(d \mid \mathcal{T}) = \frac{\rho}{2}\,\alpha(\mathcal{T})\,L(\mathcal{T})\,
\exp\Bigl[-\frac{\rho}{2}\,\alpha(\mathcal{T})\,L(\mathcal{T})\,d\Bigr], \qquad d > 0,$$

where

$$\alpha(\mathcal{T}) = 1 - \mathbb{P}(\text{tree unchanged} \mid \mathcal{T})$$

is the probability that a recombination event changes the tree. The waiting distance is therefore still
exponential, as it is for recombination events themselves, but with the intensity reduced by the thinning
factor $\alpha(\mathcal{T}) \in (0,1)$ rather than the unthinned intensity $(\rho/2)L(\mathcal{T})$ of the
recombination process.

## Depends on

- [Probability that a recombination leaves the local tree unchanged under the SMC'](smc-prime-tree-unchanging-probability.md)
- [Pairwise sequentially Markov coalescents SMC and SMC′](sequentially-markov-coalescent-smc-smc-pairwise.md)

## Proof depends on

- [Probability that a recombination leaves the local tree unchanged under the SMC'](smc-prime-tree-unchanging-probability.md)
- [Thinning](../../../Probability/point-processes/poisson-processes/thinning-2.md)
- [Arrival times of exponential interarrivals are Erlang](../../../Probability/point-processes/poisson-processes/has-law-arrival-time.md)

## Expansion

Recombination breakpoints along the genome form a Poisson process of intensity
$(\rho/2)L(\mathcal{T})$ while the tree is $\mathcal{T}$. Colour each event according to whether it
changes the tree: under the SMC' an event leaves the tree intact exactly when the detached lineage
reattaches to the branch it came from above the cut, an event of probability
$1 - \alpha(\mathcal{T})$ computed from the current tree alone. Thinning a Poisson process by an
independent colouring leaves a Poisson process of intensity scaled by the retained probability, and up to
the first tree change the tree, and hence the thinning probability, does not move. The distance to the
first retained point is then exponential with the stated rate.

## Sources

- Y. Deng, Y. S. Song and R. Nielsen, "The distribution of waiting distances in ancestral recombination graphs", Theoretical Population Biology 141 (2021), 34-43, <https://doi.org/10.1016/j.tpb.2021.06.003> (PMC8556732). (Equations 1 and 4, Theorem 2.)

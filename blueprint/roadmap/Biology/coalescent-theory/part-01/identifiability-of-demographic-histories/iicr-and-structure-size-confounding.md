# Confounding of population structure with size change in the IICR

Let $T_2$ be the coalescence time of two lineages, with the [inverse instantaneous coalescence rate](../../inverse-instantaneous-coalescence-rate/iicr-of-a-pairwise-coalescence-time.md) $\mathrm{IICR}(t) = P(T_2 > t)/f(t)$, which equals the relative size $\lambda(t)$ in a panmictic population. Mazet, Rodríguez, Grusea, Boitard and Chikhi (2016) observe that for any model, structured or not, the law of $T_2$ is reproduced exactly by the panmictic history with $\lambda = \mathrm{IICR}$, so the two cannot be distinguished from pairwise coalescence times alone; the source calls this history a fictitious population size change. In the symmetric $n$-island model with constant deme sizes and scaled migration rate $M$, writing $\gamma = M/(n - 1)$, the density of $T_2$ is a combination of two exponentials whose rates $\alpha$ and $\beta$ are the roots of a quadratic with discriminant $(1 + n\gamma)^2 - 4\gamma$, depending on whether the two genes are sampled from the same deme or from different demes, so the IICR varies in time although no deme changes size. Methods that infer size histories from pairwise coalescence, such as PSMC, therefore estimate the IICR, which coincides with a population size only in panmictic models.

## Depends on

- [Inverse instantaneous coalescence rate of a pairwise coalescence time](../../inverse-instantaneous-coalescence-rate/iicr-of-a-pairwise-coalescence-time.md)
- [Transition rates of the two-lineage structured coalescent](../../structured-coalescent/rate.md)

## Proof depends on

- [Distribution of the pairwise coalescence time in the island model](../../structured-coalescent/island-coalescence-time-distribution.md)

## Expansion

1. Regularity: a positive density and a survival function tending to $0$, so that $\lambda = \mathrm{IICR}$ defines a history whose pair coalescence time has the given law.
2. The $n$-island model: the density of $T_2$ for same-deme and different-deme samples, and the resulting non-constant IICR.
3. Statistics of larger samples, such as three-lineage coalescence times, whose laws differ between an island model and its IICR-matched panmictic history.

## Sources

- O. Mazet, W. Rodríguez, S. Grusea, S. Boitard and L. Chikhi, On the importance of being structured: instantaneous coalescence rates and human evolution—lessons for ancestral population size inference?, Heredity 116 (2016), 362–371, sections on the IICR and on linking population structure and population size change. <https://doi.org/10.1038/hdy.2015.104>

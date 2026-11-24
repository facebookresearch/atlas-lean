# Inverse instantaneous coalescence rate and confounding of structure with size

For the coalescence time $T_2$ of two lineages, with density $f$ and survival function $P(T_2 > t)$, Mazet, Rodríguez, Grusea, Boitard and Chikhi (2016) define the inverse instantaneous coalescence rate

$$\mathrm{IICR}(t) = \frac{P(T_2 > t)}{f(t)},$$

the reciprocal of the hazard rate of $T_2$. In a panmictic population with relative size $\lambda(t)$, $T_2$ has hazard $1/\lambda(t)$, so $\mathrm{IICR} = \lambda$, and conversely $\lambda$ can be recovered from the law of $T_2$. For any model, structured or not, the law of $T_2$ is reproduced exactly by the panmictic history with $\lambda = \mathrm{IICR}$, so the two cannot be distinguished from pairwise coalescence times alone; the source calls this history a fictitious population size change. In the symmetric $n$-island model with constant deme sizes, the density of $T_2$ is a combination of two exponentials whose rates $\alpha$ and $\beta$ are the roots of a quadratic with discriminant $(1 + n\gamma)^2 - 4\gamma$, depending on whether the two genes are sampled from the same deme or from different demes, so the IICR varies in time although no deme changes size. Methods that infer size histories from pairwise coalescence, such as PSMC, therefore estimate the IICR, which coincides with a population size only in panmictic models.

## Expansion

1. The IICR as the reciprocal hazard of $T_2$, and its identity with $\lambda$ in a panmictic population of relative size $\lambda$.
2. Regularity: a positive density and a survival function tending to $0$, so that $\lambda = \mathrm{IICR}$ defines a history whose pair coalescence time has the given law.
3. The $n$-island model: the density of $T_2$ for same-deme and different-deme samples, and the resulting non-constant IICR.
4. Statistics of larger samples, such as three-lineage coalescence times, whose laws differ between an island model and its IICR-matched panmictic history.

## Sources

- O. Mazet, W. Rodríguez, S. Grusea, S. Boitard and L. Chikhi, On the importance of being structured: instantaneous coalescence rates and human evolution—lessons for ancestral population size inference?, Heredity 116 (2016), 362–371, sections on the IICR and on linking population structure and population size change. <https://doi.org/10.1038/hdy.2015.104>

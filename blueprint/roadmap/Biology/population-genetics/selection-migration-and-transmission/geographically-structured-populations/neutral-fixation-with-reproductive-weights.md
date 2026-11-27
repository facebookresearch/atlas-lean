# Neutral fixation probability in a structured population

Consider the neutral structured diffusion on finitely many demes with generator $Lf = \sum_i\frac{x_i(1 - x_i)}{2\kappa_i}\partial_i^2f + \sum_i\sum_{j \ne i}q_{ij}(x_j - x_i)\partial_if$, where $q_{ij} \ge 0$ are backward migration rates forming an irreducible rate matrix $Q$ (diagonal $-\sum_{j \ne i}q_{ij}$). Let $w$ be the positive left null vector of $Q$ with $\sum_iw_i = 1$, the stationary law of the backward lineage-migration chain. Then $\bar x(t) = \sum_iw_ix_i(t)$ is a bounded martingale, the path is absorbed in finite time at one of the two monomorphic states $x = 0$ or $x = 1$, and the probability that the allele fixes in every deme is

$$P_x(\text{fixation}) = \sum_iw_ix_i.$$

With conservative migration the weights are the census weights, $w_i = \kappa_i/\sum_k\kappa_k$, and the fixation probability is the allele's overall frequency, whatever the migration rates; this is the neutral case of the invariance of Maruyama (1970, Summary), who showed that the fixation probability of a mutant is not altered by subdivision into partially isolated colonies when fitness is additive, sampling and selection act separately in each colony, and migration does not change the gene frequency in the whole population. The weighted formula for non-conservative migration is this page's derivation, proved below.

Proof. Applying $L$ to $f(x) = \sum_iw_ix_i$ gives $\sum_iw_i\sum_jQ_{ij}x_j = (w^TQx) = 0$, since the second-order part vanishes on linear functions; so $\bar x$ is a martingale with values in $[0, 1]$. The states $x = 0$ and $x = 1$ are absorbing. From any non-monomorphic state the local resampling of the demes and the irreducible migration move the path to a monomorphic state with probability bounded below over a time interval of fixed length, so absorption occurs in finite time almost surely. Optional stopping at the absorption time $\tau$ gives $\sum_iw_ix_i = E_x[\bar x(\tau)] = P_x(x(\tau) = 1)$.

## Depends on

- [Which weighted frequency migration conserves](../../../../Biology/population-genetics/selection-migration-and-transmission/geographically-structured-populations/conservation-under-migration.md)
- [Dynkin's formula and optional stopping for diffusions on the unit interval](../../../../Probability/stochastic-calculus/one-dimensional-diffusions/dynkin-formula-and-stopping.md)

## Expansion

1. The structured neutral diffusion and its two absorbing states.
2. The martingale property of $\bar x$ from $w^TQ = 0$.
3. Almost sure absorption in finite time, from irreducibility of migration and local drift.
4. Optional stopping at the absorption time, and the conservative case with census weights.

## Sources

- T. Maruyama, On the fixation probability of mutant genes in a subdivided population, Genet. Res. 15 (1970), 221–225, Summary. <https://doi.org/10.1017/S0016672300001543>
- M. C. Whitlock, Fixation probability and time in subdivided populations, Genetics 164 (2003), 767–779, abstract. <https://doi.org/10.1093/genetics/164.2.767>

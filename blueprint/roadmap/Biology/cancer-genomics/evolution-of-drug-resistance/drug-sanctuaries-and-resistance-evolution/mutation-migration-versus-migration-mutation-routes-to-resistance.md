# Mutation-migration versus migration-mutation routes to resistance

In the [two-compartment drug-sanctuary model](two-compartment-branching-model-of-a-drug-sanctuary.md), assume the rugged landscape created by drug heterogeneity: in the sanctuary both types grow but resistance is costly ($b_{00} > d_{00}$, $b_{10} > d_{10}$, $b_{10} < b_{00}$), while in the drug compartment sensitive cells are subcritical and resistant cells supercritical ($b_{01} < d_{01}$, $b_{11} > d_{11}$, $b_{11} > b_{01}$). Resistant cells can reach the drug compartment either by **mutation then migration** (resistance arises in the sanctuary, then a resistant cell migrates) or by **migration then mutation** (a sensitive cell migrates and its subcritical lineage produces a resistant mutant). In the limit of small mutation probability and migration rate, the mutation-migration route is the faster one if and only if

$$\frac{b_{00}}{(b_{00} - d_{00}) - (b_{10} - d_{10})} > \frac{b_{01}}{(b_{00} - d_{00}) - (b_{01} - d_{01})}.$$

If death rates are equal in all types and compartments and the costs are parametrized as $b_{10} = (1 - s) b_{00}$ (cost of resistance in the sanctuary) and $b_{01} = (1 - \delta) b_{00}$ (cost of sensitivity under drug), the condition becomes

$$\delta > \frac{s}{1 + s}.$$

## Depends on

- [Two-compartment branching-process model of a drug sanctuary](two-compartment-branching-model-of-a-drug-sanctuary.md)

## Expansion

With equal death rates, $(b_{00} - d_{00}) - (b_{10} - d_{10}) = s b_{00}$ and $(b_{00} - d_{00}) - (b_{01} - d_{01}) = \delta b_{00}$, so the general inequality reads $1/s > (1 - \delta)/\delta$, i.e. $\delta > s(1 - \delta)$, i.e. $\delta(1 + s) > s$. A potent targeted therapy has $\delta > s$, so the condition is expected to hold in most cases: resistance is most likely to arise first in the sanctuary, where sensitive cells keep proliferating, and to seed the drug-exposed compartment from there. Numerical solution of the backward equations further shows that spatial drug heterogeneity accelerates resistance only below a threshold migration rate; very frequent migration exposes cells to the drug compartment more often and delays resistance.

## Sources

- F. Fu, M. A. Nowak and S. Bonhoeffer, "Spatial heterogeneity in drug concentrations can facilitate the emergence of resistance to cancer therapy", PLoS Computational Biology 11 (2015), e1004142, <https://doi.org/10.1371/journal.pcbi.1004142> (PMC4366398). Results, Equations (1)-(2); derivation in S1 Text.

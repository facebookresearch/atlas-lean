# Resistance-distance approximation of expected coalescence times

**Model.** Demes are the vertices $V$ of a connected undirected graph $G = (V, E)$ (in practice a regular triangular grid), with a symmetric effective migration rate $m_e > 0$ on every edge $e \in E$ and an effective diversity rate $q_\alpha > 0$ for every deme $\alpha$. Let $T_{\alpha\beta}(m, q)$ be the expected coalescence time of two haploid lineages sampled from demes $\alpha$ and $\beta$ under the corresponding stepping-stone model, and let $R_{\alpha\beta}(m)$ be the effective resistance between $\alpha$ and $\beta$ when $G$ is an electrical network with conductance $m_e$ on edge $e$.

**Approximation.** The between-deme part of the coalescence time is approximated by resistance,

$$\frac{R_{\alpha\beta}}{4} \approx T_{\alpha\beta} - \frac{T_{\alpha\alpha} + T_{\beta\beta}}{2},$$

and the within-deme parts are replaced by the diversity parameters, giving

$$T_{\alpha\beta}(m, q) \approx \frac{R_{\alpha\beta}(m)}{4} + \frac{q_\alpha + q_\beta}{2}.$$

The relation is exact when migration is isotropic (all demes equivalent with respect to the rate and pattern of migration), and it improves as migration rates increase. All pairwise resistances follow from one pseudo-inversion of the $d \times d$ weighted graph Laplacian, $R_{\alpha\beta} = L^+_{\alpha\alpha} + L^+_{\beta\beta} - 2L^+_{\alpha\beta}$, at cost $O(d^3)$ for $d$ demes, instead of the $O(d^6)$ needed to solve the $d(d+1)/2$ linear first-step equations for all $T_{\alpha\beta}$.

**Voronoi prior.** Migration rates are parametrized by a Voronoi tessellation of the habitat into cells $c$ with rates $\log_{10} m_c = \mu + e_c$; an edge between demes $\alpha$ and $\beta$ gets $m_{\alpha\beta} = (m_{c_\alpha} + m_{c_\beta})/2$, where $c_\alpha$ is the cell containing $\alpha$. The number and positions of cells are sampled by reversible-jump MCMC, and averaging the posterior over tessellations yields a smooth effective migration surface.

## Remarks

Effective resistance integrates over all paths between two demes, weighting parallel routes like parallel resistors, which is the circuit-theory counterpart of averaging over all migration histories of the two lineages; this "isolation by resistance" is what lets local barriers lower gene flow over large distances. The combination $T_{\alpha\beta} - (T_{\alpha\alpha} + T_{\beta\beta})/2$ is the expected excess of between-deme over within-deme coalescence time, which in the [island model](../../../coalescent-theory/structured-coalescent/mean-coalescence-time.md) depends on the number of demes and the migration rate but not on the deme size; the approximation keeps that structure on a general graph. Treating $q$ as free parameters decouples local diversity (which is sensitive to ascertainment) from the migration surface.

## Sources

- D. Petkova, J. Novembre and M. Stephens, "Visualizing spatial population structure with estimated effective migration surfaces", Nature Genetics 48 (2016), 94–100, Online Methods (Equations (9)–(12)), <https://doi.org/10.1038/ng.3464>, PMCID PMC4696895.
- B. H. McRae, "Isolation by resistance", Evolution 60 (2006), 1551–1561, <https://doi.org/10.1111/j.0014-3820.2006.tb00500.x>.

# Extinction threshold and occupancy-model limit of the Wright-Fisher seed-bank metapopulation

**Model ($k$-parent WFSB metapopulation, parameters $(M,H,g,c,p)$).** Patches $i\in\mathbb{Z}$ lie on a line, each with $M$ seed-bank compartments holding one seed, either a ghost (type $0$) or real (type $1$), together with its age. Each generation:
1. In every patch exactly $\lfloor gM\rfloor$ uniformly chosen seeds germinate; real seeds produce real plants only if they are at most $H$ generations old (maximal dormancy $H$), otherwise ghost plants.
2. Each patch independently suffers an extinction event with probability $p$, turning all its juvenile plants into ghosts.
3. Each emptied compartment receives a new seed: $k\ge2$ potential parents are sampled with replacement, each from the same patch with probability $1-2c$ and from each neighbouring patch with probability $c$ ($c\in(0,1/2)$); the seed is real if at least one sampled parent is real (strong selection against ghosts), and ghost otherwise.
4. Remaining seeds stay dormant and age by one.

The associated *occupancy process* records, for each patch, whether it holds a viable real seed and the age of its youngest one. The *best occupancy achievable* (BOA) process with parameters $(H,p)$ is the stochastic patch occupancy model in which a non-extinct patch holding a seed of age at most $H$ recolonizes itself and both neighbours with fresh seeds, while other patches just age.

**Statements.**
1. *(Extinction threshold.)* For every $H\in\mathbb{N}$ there is $p_{\mathrm{crit}}(H)\in(0,1)$ such that for all $M$, $k\ge2$, $g\in(0,1)$, $c\in(0,1/2)$ and all initial conditions, if $p>p_{\mathrm{crit}}(H)$ then almost surely no patch eventually holds a viable real seed: the real population goes extinct. $p_{\mathrm{crit}}(H)$ is the critical parameter of the BOA process (an oriented-percolation-type survival threshold), and it increases with $H$, so a longer-lived seed bank tolerates more frequent extinctions.
2. *(Domination.)* Driven by the same extinction events, the $k$-parent occupancy process is dominated by the BOA process at all times, patch by patch.
3. *(SPOM limit.)* If $k=\lceil M^\alpha\rceil$ with $\alpha>1$, then for every finite horizon $N$ the probability that the occupancy process and the BOA process agree on all patches up to generation $N$ tends to $1$ as $M\to\infty$.

## Expansion

The BOA process is the best case for the real type: given the extinction pattern, a patch can hold viable real seeds only if a chain of non-extinct patches within dormancy windows connects it to an initially occupied patch, which is exactly an oriented percolation cluster in space-time with "memory" $H$. Coupling the metapopulation to the BOA process on the same extinction variables gives the domination, so extinction of the BOA process (for $p$ above its critical value) forces extinction of real plants for any patch size and selection strength. Conversely, when $k\gg M$, a single real plant among $M$ is sampled as a parent with overwhelming probability and the germination and sampling deviations listed above become negligible, so the individual-based model follows the BOA dynamics.

## Sources

- Apolline Louvet, "Extinction threshold and large population limit of a plant metapopulation model with recurrent extinction events and a seed bank component", Theoretical Population Biology 145 (2022), 22–37, <https://doi.org/10.1016/j.tpb.2022.02.003>; numbering as in arXiv:2107.13359: Section 1 (model definition, BOA and occupancy processes, Theorems 1.9 and 1.10), Section 3 (Proposition 3.1, Corollary 3.2, Proposition 3.3), Appendix (numerical computation of $p_{\mathrm{crit}}(H)$).

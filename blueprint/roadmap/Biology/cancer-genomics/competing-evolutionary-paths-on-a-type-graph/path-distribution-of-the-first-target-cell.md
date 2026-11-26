# Path distribution of the first target cell

**Setting.** The multitype birth–death–transition process on a directed acyclic type graph, root $1$ with the largest positive net growth rate $\lambda$, target $N$, path weights $w(p) = \nu(p_1,p_2)\prod_{i=2}^{l}\nu(p_i,p_{i+1})/(\lambda - \lambda(p_i))$ and total weight $\phi_N$. For a root-to-target path $p$, let $T(p)$ be the first time a cell with vertex lineage $p$ exists, and $T(\neg p) = \min_{q \ne p} T(q)$. Let $P_1$ denote probability conditional on survival of the root population.

**Theorem.** For small target-seeding rates and $t \in \mathbb R$,

$$P_1\big(T(\neg p) - T(p) > t\big) \approx \frac{w(p)}{w(p) + e^{\lambda t}\sum_{q \ne p} w(q)} .$$

At $t = 0$: the target is first populated via path $p$ with probability

$$P_1\big(T(p) = T\big) \approx \frac{w(p)}{\phi_N},$$

and via a set of paths with the sum of these probabilities. The lead of the winning path over the rest is logistic with scale $1/\lambda$.

**Fitness valleys.** With two routes to a double mutant, direct $1 \to 3$ at rate $\nu^2$ and stepwise $1 \to 2 \to 3$ at rate $\nu$ per step through a less fit intermediate, the weights are $\nu^2$ and $\nu^2/(\lambda - \lambda(2))$, so the stepwise path through the valley is the more likely route iff the fitness cost satisfies $\lambda - \lambda(2) < 1$ (in the time units of the rates), regardless of $\nu$.

## Depends on

- [Path weights and the target hitting time on a type graph](path-weights-and-the-target-hitting-time.md)

## Expansion

Conditionally on the root amplitude $W$, cells of lineage $p$ seed the target as independent Poisson processes with intensities approximately $w(p)We^{\lambda t}$, proportional across paths; the first arrival therefore picks path $p$ with probability proportional to $w(p)$, and the gap between the competing Gumbel-type arrival times gives the logistic form after $W$ cancels. Applied to bacteria, the weights compare stepwise versus direct multidrug resistance and mutation-then-migration versus migration-then-mutation routes in drug sanctuaries.

## Sources

- M. D. Nicholson, T. Antal, "Competing evolutionary paths in growing populations with applications to multidrug resistance", PLoS Computational Biology 15(4) (2019) e1006866, Path distribution section, equation (10), Theorem 2 and the fitness-valley example with two paths, <https://doi.org/10.1371/journal.pcbi.1006866>, PMCID: PMC6483269.

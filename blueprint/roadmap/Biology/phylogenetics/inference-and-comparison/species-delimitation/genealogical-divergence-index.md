# Genealogical divergence index

**Setting.** Two populations $A$ and $B$ split at time $\tau_{AB}$ (in expected mutations per site) from a common ancestor; population $A$ has population size parameter $\theta_A = 4N_A\mu$. Sample two sequences $a_1, a_2$ from $A$ and one sequence $b$ from $B$, and let

$$P_1 = \Pr\big(\text{gene tree } ((a_1, a_2), b)\big) \qquad \text{(Eq. 5)}$$

under the multispecies coalescent, possibly with migration. $P_1$ ranges from $1/3$ (all three sequences exchangeable) to $1$.

**Definition.** The genealogical divergence index is the rescaling

$$\mathrm{gdi} = \frac{3P_1 - 1}{2} \in [0, 1] \qquad \text{(Eq. 6)}.$$

**Proposition (no migration).** Without gene flow,

$$P_1 = 1 - \tfrac{2}{3}\,e^{-2\tau_{AB}/\theta_A}, \qquad \mathrm{gdi} = 1 - e^{-2\tau_{AB}/\theta_A} \qquad \text{(Eq. 7)},$$

where $e^{-2\tau_{AB}/\theta_A}$ is the probability that $a_1$ and $a_2$ do not coalesce in $A$ before reaching the split.

**Heuristic.** The rule of thumb $\mathrm{gdi} < 0.2$ (single species), $\mathrm{gdi} > 0.7$ (distinct species), and ambiguous in between corresponds to $P_1 = 0.47$ and $0.8$, and without migration to divergences $2\tau_{AB}/\theta_A \approx 0.22$ and $1.20$ coalescent units. With migration $P_1$ can be computed exactly from the 21-state Markov chain of coalescence and migration for three sequences, using the spectral decomposition of its rate matrix.

## Expansion

Without migration, $a_1$ and $a_2$ coalesce in $A$ before $\tau_{AB}$ with probability $1 - e^{-2\tau_{AB}/\theta_A}$, since two lineages coalesce at rate $2/\theta_A$ in mutational time units; this always yields $((a_1,a_2),b)$. Otherwise all three lineages enter the ancestral population, where each of the three topologies is equally likely, contributing $\tfrac13 e^{-2\tau_{AB}/\theta_A}$. Adding gives $P_1$, and the rescaling gives $\mathrm{gdi}$. The source shows that Bayesian model selection under the multispecies coalescent prefers the two-species model asymptotically in the number of loci whenever populations are partially isolated, even with substantial gene flow, so it delimits structure rather than species; the gdi is one proposed heuristic for deciding when divergence is large enough to call two species.

## Sources

- A. D. Leaché, T. Zhu, B. Rannala, Z. Yang, "The spectre of too many species", Systematic Biology 68(1) (2019) 168–181, section "Heuristic Species Delimitation", Eqs. 5–7 and Table 1, <https://doi.org/10.1093/sysbio/syy051> (PMC6292489).
- N. D. Jackson, B. C. Carstens, A. E. Morales, B. C. O'Meara, "Species delimitation with gene flow", Systematic Biology 66 (2017) 799–812.

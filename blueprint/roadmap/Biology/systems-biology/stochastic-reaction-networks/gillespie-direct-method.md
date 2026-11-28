# Gillespie direct method (stochastic simulation algorithm)

Let a chemical reaction network have reactions $1, \dots, R$ with propensities $\alpha_r(x) \ge 0$, and let
$a_0(x) = \sum_r \alpha_r(x)$. One step of the direct method from state $x$: if $a_0(x) = 0$, the state is absorbing and the
simulation stops; otherwise draw independent $u_1, u_2$ uniform on $(0,1)$, set the holding time $\tau = \ln(1/u_1)/a_0(x)$,
choose the least $j$ with $\alpha_1(x) + \dots + \alpha_j(x) > u_2\, a_0(x)$, advance time by $\tau$ and apply reaction $j$.
Null reactions, whose product and reactant vectors agree, change time but not state; they are either excluded from the
network or kept with that effect, as stated. The first-reaction and next-reaction methods are separate
definitions.

## Expansion

This node states a precise definition. A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: stochastic chemical reaction networks with mass-action propensities and their continuous-time Markov chain semantics.

## Sources

- Exact Stochastic Simulation of Coupled Chemical Reactions — D. T. Gillespie, J. Phys. Chem. 81(25):2340-2361, 1977, Steps 0–3 of the direct method. <https://www.cl.cam.ac.uk/teaching/2425/Bioinfo/papers/DanielGillespie1.pdf>
- Stochastic Simulation: Lecture 9 (chemical kinetics) — M. Giles, University of Oxford. <https://people.maths.ox.ac.uk/gilesm/mc/stoch_sim/lec9.pdf> SSA slides (exact simulation, exponential jump intervals, Next Reaction Method).

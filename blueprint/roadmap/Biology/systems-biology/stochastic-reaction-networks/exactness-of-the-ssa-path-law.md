# Exactness of the SSA path law

Let a chemical reaction network have its stochastic semantics as a continuous-time Markov chain on $\mathbb{N}^S$, and use ideal
independent uniform random numbers. From every non-absorbing state $x$, one step of the direct method produces a holding
time with law $\mathrm{Exp}(a_0(x))$, independent of the chosen reaction, and the reaction $j$ with probability
$\alpha_j(x)/a_0(x)$; aggregating reactions with the same successor state, the step has the jump law of the chain.
Consequently, up to the explosion time (or on every finite horizon, if the chain does not explode), the law of the
simulated path equals the path law of the chain. Null reactions affect only the jump-chain description, not the path law
of states.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Stochastic chemical reaction networks (mass-action CTMC semantics).
- Statement prerequisite: Holding times, jump chain and path law up to explosion of a continuous-time Markov chain on a countable state space.

## Depends on

- [Gillespie direct method (stochastic simulation algorithm)](gillespie-direct-method.md)
- [Stochastic mass-action propensity](../stochastic-mass-action-metabolic-control-and-flu/propensity.md)
- [State after one reaction firing](../stochastic-mass-action-metabolic-control-and-flu/fire.md)

## Related topics

- [Jump matrix of a rate matrix](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-matrix.md)

## Sources

- Exact Stochastic Simulation of Coupled Chemical Reactions — D. T. Gillespie, J. Phys. Chem. 81(25):2340-2361, 1977, Sec. III, eqs. (15), (18) and (21). <https://www.cl.cam.ac.uk/teaching/2425/Bioinfo/papers/DanielGillespie1.pdf>
- Stochastic Simulation: Lecture 9 (chemical kinetics) — M. Giles, University of Oxford, SSA is an exact simulation algorithm. <https://people.maths.ox.ac.uk/gilesm/mc/stoch_sim/lec9.pdf>

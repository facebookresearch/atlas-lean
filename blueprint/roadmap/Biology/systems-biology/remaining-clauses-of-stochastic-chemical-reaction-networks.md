# Gillespie propensities and the mass-action Markov chain of a reaction network

Holding and jump times of the stochastic semantics of chemical reaction networks are separate definitions and are not part
of this node; nor are the reaction network, the mass-action propensity with falling factorials and the state after a firing,
which have their own pages. This node collects the remaining model clauses.

## Expansion

A sound expansion has separate pages for:

1. **Reactions.** A network has finitely many species $S$ and reactions $r$ given by reactant and product vectors $a_r, b_r \in \mathbb{N}^S$
   and rate constants $k_r > 0$; null reactions ($a_r = b_r$) are excluded or handled by a stated convention.
2. **Mass-action propensities.** In Gillespie's convention $\alpha_r(x) = c_r \prod_s \binom{x_s}{a_{r,s}}$, the number of distinct
   reactant combinations times $c_r$; it equals the falling-factorial propensity with $k_r = c_r / \prod_s a_{r,s}!$, and
   volume factors are absorbed into the constant.
3. **Compatibility.** The stochastic semantics is the continuous-time Markov chain on $\mathbb{N}^S$ with jump $x \to x + b_r - a_r$ at rate
   $\alpha_r(x)$, matching the holding- and jump-time definitions up to explosion.

## Depends on

- [Chemical reaction network](../../Dynamics/smooth-dynamics/reaction-network.md)
- [Stochastic mass-action propensity](stochastic-mass-action-metabolic-control-and-flu/propensity.md)
- [State after one reaction firing](stochastic-mass-action-metabolic-control-and-flu/fire.md)

## Related topics

- [Generator of the mass-action chain on a finite state class](stochastic-mass-action-metabolic-control-and-flu/class-generator.md)

## Sources

- Exact Stochastic Simulation of Coupled Chemical Reactions — D. T. Gillespie, J. Phys. Chem. 81(25):2340-2361, 1977, Sec. IIIA, eq. (15). <https://www.cl.cam.ac.uk/teaching/2425/Bioinfo/papers/DanielGillespie1.pdf>
- Programmability of Chemical Reaction Networks — M. Cook, D. Soloveichik, E. Winfree, J. Bruck, Sec. 2.1, eqs. (1) and (2) (falling-factorial rates with volume; continuous-time Markov process). <https://users.cs.duke.edu/~reif/courses/molcomplectures/DNA.HybridizationReactions/ComplexityChemicalReactionNetworks/ComplexityChemicalReactionNetworksBruck.pdf>

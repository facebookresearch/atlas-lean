# Computational power of stochastic CRNs: universal with error, limited without

This node collects the computational power of stochastic chemical reaction networks, after Soloveichik, Cook,
Winfree and Bruck.

## Expansion

A sound expansion has separate pages for:

1. **Bounded-error universality.** Under well-mixed stochastic kinetics, a chemical reaction network with finitely many
   species simulates a register machine, and hence a Turing machine, with error probability bounded by any prescribed
   $\varepsilon > 0$ for the whole computation, with the time overhead and output/halting convention of the source.
2. **Zero-error limitation.** Computation that is correct with probability one is not Turing universal: the questions it
   depends on are reachability questions for vector addition systems (Petri nets), which are decidable.
3. **Probabilities.** Questions about the probability of behaviours of stochastic networks are undecidable, a
   different question from reachability.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Turing machine.

## Depends on

- [CRNs as computing devices](crns-as-computing-devices.md)

## Sources

- Programmability of Chemical Reaction Networks — M. Cook, D. Soloveichik, E. Winfree, J. Bruck, Sec. 1 (zero-error limitation and decidable reachability), Theorem 3 (undecidable probabilities), Definition 5 and Theorem 4 (register machines with error at most ε), Theorem 6 (Turing machines with polynomial slowdown). <https://users.cs.duke.edu/~reif/courses/molcomplectures/DNA.HybridizationReactions/ComplexityChemicalReactionNetworks/ComplexityChemicalReactionNetworksBruck.pdf>

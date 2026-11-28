# CRNs as computing devices

Fix a chemical reaction network with designated input and output species, an input encoding as initial molecular
counts, and an output read from the counts of the output species (or from the presence of yes/no voting species for
predicates). The network stably computes a function (or decides a predicate) if from every initial state encoding an
input, every reachable state can reach a state from which every reachable state has the correct output. It computes
with bounded error $\varepsilon$ if, under the stochastic (continuous-time Markov chain) semantics, the output read at the
designated halting event or in the limit is correct with probability at least $1 - \varepsilon$; halting and readout
conventions are part of the definition. Time is measured as expected continuous-time Markov chain time to the stated
event. These notions are distinct.

## Expansion

This node states a precise definition.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Stochastic chemical reaction networks (mass-action CTMC semantics).

## Sources

- Programmability of Chemical Reaction Networks — M. Cook, D. Soloveichik, E. Winfree, J. Bruck, Sec. 2.1 (stochastic semantics, expected times), Sec. 3 (probability-one output) and Sec. 6.1, Definition 5 (computation with error at most ε). <https://users.cs.duke.edu/~reif/courses/molcomplectures/DNA.HybridizationReactions/ComplexityChemicalReactionNetworks/ComplexityChemicalReactionNetworksBruck.pdf>
- Deterministic function computation with chemical reaction networks — H.-L. Chen, D. Doty, D. Soloveichik, arXiv:1204.4176, Sec. 2.2 (stable decidability of predicates, after Angluin, Aspnes and Eisenstat) and Sec. 2.3 (stable computation of functions). <https://arxiv.org/abs/1204.4176>

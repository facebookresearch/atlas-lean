# Runaway and divergent reactions in enzymatic assembly lines

**Model.** An oligomer is a rooted tree of monomers of finitely many types; a compartment contains a finite set of enzymes, each of which adds one donor monomer at a specific position of a matching acceptor-substrate. With monomers in excess and oligomers growing independently, growth in a compartment is a continuous-time Markov chain whose states are oligomers and whose transitions are single-monomer additions, with rates proportional to enzyme concentrations; the oligomer exits after a residence time $T$. The reachable states from an input oligomer form an acyclic **reaction network**; a state with no outgoing reaction is **terminal**. Enzyme specificity is classified as *context-free* (the acceptor-substrate is a monomer type), *branch-sensitive* (a monomer type having or lacking specific branches) or *root-sensitive* (a monomer type with a specific chain to the root).

For context-free and branch-sensitive enzymes, the **linkage network** of a compartment is the directed graph on monomer types (plus *triggers*, branched acceptor-substrates that cannot be synthesized inside the compartment) with an arrow from acceptor type to donor type whenever some enzyme can perform that linkage. Two enzymes form an **acceptor block** if the action of one prevents the later action of the other: bidirectionally (they compete for the same acceptor-substrate) or, for branch-sensitive enzymes, unidirectionally (the acceptor-substrate of one lies on a branch of the other's).

- A **runaway reaction** is an infinite path in the reaction network (unbounded tandem repeats).
- A **divergent reaction** is a fork in the reaction network beyond which paths never reconverge.

**Lemma 1.** A compartment has a runaway reaction if and only if its linkage network contains a directed cycle (a linkage loop). Ideal root-sensitive enzymes admit no runaway reactions.

**Lemma 2.** A divergent reaction implies an acceptor block. For root-sensitive and context-free enzymes the converse holds as well (only bidirectional blocks are possible); for branch-sensitive enzymes an acceptor block need not produce divergence.

**Remark (full conversion).** An input oligomer is converted to a single final oligomer with probability tending to one as $T \to \infty$ if and only if the compartment has no runaway and no divergent reactions; for finite $T$, intermediates exit with positive probability (truncated reactions).

## Expansion

Lemma 1, forward direction: an infinite path adds monomers forever, so some root-to-tip chain grows without bound; with finitely many monomer types two added monomers on that chain have the same type, which is a cycle in the linkage network. Conversely, a cycle lets a branch containing another copy of the starting monomer type be grown on that type, and the step can be iterated indefinitely, in the manner of the pumping lemma for regular languages. Root-sensitive enzymes act at a fixed depth, so chains are bounded.

Lemma 2: at a fork two enzymes can act on the same oligomer; if each could still act after the other, the two orders would reconverge. So one enzyme's action disables the other. For context-free and root-sensitive specificities this can only happen by competing for the same acceptor site, after which no path can undo the choice; for branch-sensitive enzymes a later enzyme can restore a common descendant.

Remark: as $T \to \infty$ the exit probability of every non-terminal state of a finite acyclic chain tends to zero, so the output law concentrates on terminal states and arbitrarily long tandem repeats; it is a point mass iff the network is finite with a unique terminal state.

## Sources

- A. Jaiman, M. Thattai, "Golgi compartments enable controlled biomolecular assembly using promiscuous enzymes", eLife 9 (2020) e49573, Table 1 and Appendix 2 (Remarks 1–2, Lemmas 1–2), <https://doi.org/10.7554/eLife.49573>, PMCID PMC7360365.

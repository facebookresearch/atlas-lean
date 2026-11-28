# Configuration reachability and boundedness of asynchronous programs with cancel are undecidable

Once handlers can cancel all pending instances of a handler, asynchronous programs can simulate Petri nets with reset arcs, so deciding whether a given configuration is reachable, or whether the reachable configurations are finitely many, becomes impossible.

**Theorem.** For [asynchronous programs with cancel](asynchronous-programs-with-cancel.md):

1. the configuration reachability problem (given a program $\mathcal{P}$ and a configuration $(d, \mathbf{m})$, is $(d, \mathbf{m})$ reachable from the initial configuration?) is undecidable;
2. the boundedness problem (given $\mathcal{P}$, is its set of reachable configurations finite?) is undecidable.

The safety problem (global state reachability) for asynchronous programs with cancel remains decidable.

## Depends on

- [Asynchronous programs with cancel](asynchronous-programs-with-cancel.md)
- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces the reachability and boundedness problems for Petri nets with reset arcs, both undecidable by Dufourd, Finkel and Schnoebelen. As for ordinary Petri nets, a net is simulated by a program in which a pending instance of handler $p$ stands for a token in place $p$: a dispatcher handler picks a transition and records its preset in the global state, the handlers of the places consume the required tokens one by one, and the outputs are posted; cancel implements the resets. The reset net is unbounded exactly when the program is, and a marking is reachable exactly when the corresponding configuration is. Decidability of safety comes from the converse translation of programs with cancel into reset nets, where coverability is decidable.

## Sources

- Pierre Ganty and Rupak Majumdar, "Algorithmic verification of asynchronous programs", *ACM Transactions on Programming Languages and Systems* 34(1), Article 6, 48 pages, 2012, <https://doi.org/10.1145/2160910.2160915>; read as arXiv:1011.0551v3, <https://arxiv.org/abs/1011.0551v3>: the theorem of Section 7.5 (items 2 and 3, with item 1 for safety), its proof and the reset-net construction of Section 7.4; the reset-net results it uses are recalled in Section 7.3.
- Catherine Dufourd, Alain Finkel and Philippe Schnoebelen, "Reset nets between decidability and undecidability", *Automata, Languages and Programming (ICALP 1998)*, Lecture Notes in Computer Science 1443, pages 103-115, Springer, 1998, <https://doi.org/10.1007/BFb0055044>: decidability of coverability and undecidability of reachability and boundedness for reset nets, as recalled in Section 7.3 of the version of the first source read.

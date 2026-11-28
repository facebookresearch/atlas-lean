# The order problem is undecidable for contracting automata groups

No algorithm computes, from a finite state transducer generating a contracting group and a state $s$, the order of $s$ in the group; this holds already for nuclear transducers.

**Theorem (Bartholdi and Mitrofanov).** There is no algorithm that, given a finite state transducer $\Phi\colon A \times S \to S \times A$ (as defined on the linked page, so that each state permutes the first letter) and $s \in S$, determines the [order](../../../presentations-and-decision-problems/conjugacy-order-and-power-problems/order-and-power-problems/order-problem.md) of $s$ in the [automaton group](functionally-recursive-group.md) $\langle \Phi \rangle$, that is, the cardinality of $\langle s \rangle$ (Theorem B of the source). This remains true when the input is restricted to nuclear transducers, which generate contracting groups (Theorem C, stated precisely as Theorem 3.4).

The source also proves the corresponding statements for the cardinality of the orbit of $a^\infty$ under $\langle s\rangle$ (Theorem B′, also for nuclear transducers), and that some automata group has states $s, t$ for which $\{n \in \mathbb{N} : st^n \text{ has finite order}\}$ is not recursive (Theorem B″). Gillibert proved independently that some automaton group has undecidable order problem; see [that page](automaton-group-undecidable-order-problem.md).

## Depends on

- [Functionally recursive groups and contracting automata groups](functionally-recursive-group.md)
- [Order problem and torsion problem of a finitely generated group](../../../presentations-and-decision-problems/conjugacy-order-and-power-problems/order-and-power-problems/order-problem.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

A Minsky machine $M$ is encoded in a finite state transducer $\Phi_M$ so that $M$ halts if and only if a chosen element has finite order in $\langle \Phi_M \rangle$ (Proposition 3.1 of the source), and the halting problem for Minsky machines is undecidable (Proposition 2.2); composing $\Phi_M$ with auxiliary transducers $\Phi_0, \Phi_1, \dots, \Phi_\ell$ gives a transducer $\Phi' = \Phi_M \circ \Phi_0 \circ \Phi_1 \circ \cdots \circ \Phi_\ell$ that generates a contracting group and keeps the equivalence (Proposition 3.6), and replacing its state set by the nucleus and its alphabet by $A^n$ then gives a nuclear transducer for the same group, so the order problem is undecidable even for contracting automata groups, whose word problem is decidable in logarithmic space.

## Sources

- Laurent Bartholdi and Ivan Mitrofanov, "The word and order problems for self-similar and automata groups", *Groups, Geometry, and Dynamics* 14(2):705–728, 2020, doi:[10.4171/GGD/560](https://doi.org/10.4171/GGD/560). Numbering of the version read, arXiv:1710.10109v4: Theorems B, B′, B″ and C, Proposition 2.2, Section 3 (Proposition 3.1), and Theorem 3.4, Proposition 3.6 and Definition 3.3 in Section 3.4.

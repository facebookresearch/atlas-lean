# The word problem is undecidable for functionally recursive groups

No algorithm decides, given an asynchronous transducer $\Phi$ and a generator $s$, whether $s$ is the identity in the functionally recursive group presented by $\Phi$.

**Theorem (Bartholdi and Mitrofanov).** There is no algorithm that, given a finite alphabet $A$, a finite set $S$, an asynchronous transducer $\Phi\colon A \times S \to F_S \times A$ (as defined on the linked page, so that each generator permutes the first letter) and $s \in S$, determines whether $s = 1$ in the [functionally recursive group](functionally-recursive-group.md) $\langle \Phi \rangle$ (Theorem A of the source).

The source also proves that no algorithm decides, given such $\Phi$, a letter $a \in A$ and $s \in S$, whether the infinite word $a^\infty$ is fixed by $s$ (Theorem A′), and that there is a single functionally recursive group $\langle \Phi \rangle$ for which $\{w \in F_S : w = 1 \text{ in } \langle \Phi \rangle\}$ is not recursive (Theorem A″). By contrast, automata groups have decidable word problem.

## Depends on

- [Functionally recursive groups and contracting automata groups](functionally-recursive-group.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof encodes a Minsky machine (a finite automaton with two counters valued in $\mathbb{N}$) in a transducer $\Phi_M$: a configuration $(s, m, n)$ of the machine is encoded in the group element $s x^{2^m} y^{2^n}$, whose recursive action follows the machine's moves; an auxiliary element $t$ detects the final state, $g = (s_* x y)\, t\, (s_* x y)^{-1}$ fixes a prescribed ray iff the machine never halts (Section 1.3), and the commutator $[g, u]$ with a further generator $u$ is trivial iff the machine does not halt (Proposition 2.4). Since the halting problem for Minsky machines is undecidable (Proposition 2.2 of the source), so is the word problem for the family of groups $\langle \Phi_M \rangle$.

## Sources

- Laurent Bartholdi and Ivan Mitrofanov, "The word and order problems for self-similar and automata groups", *Groups, Geometry, and Dynamics* 14(2):705–728, 2020, doi:[10.4171/GGD/560](https://doi.org/10.4171/GGD/560). Numbering of the version read, arXiv:1710.10109v4: Theorems A, A′ and A″, and Section 1.3 (sketch of proofs), and Section 2 (Proposition 2.2, Proposition 2.4 and the proofs in Sections 2.1–2.3).

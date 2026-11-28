# The word problem is undecidable for functionally recursive groups

No algorithm decides, given an asynchronous transducer $\Phi$ and a generator $s$, whether $s$ is the identity in the functionally recursive group presented by $\Phi$.

**Theorem (Bartholdi and Mitrofanov).** There is no algorithm that, given a finite alphabet $A$, a finite set $S$, a map $\Phi\colon A \times S \to F_S \times A$ and $s \in S$, determines whether $s = 1$ in the [functionally recursive group](functionally-recursive-group.md) $\langle \Phi \rangle$ (Theorem A of the source).

The source also proves that no algorithm decides, given such $\Phi$, a letter $a \in A$ and $s \in S$, whether the infinite word $a^\infty$ is fixed by $s$ (Theorem A′), and that there is a single functionally recursive group $\langle \Phi \rangle$ for which $\{w \in F_S : w = 1 \text{ in } \langle \Phi \rangle\}$ is not recursive (Theorem A″). By contrast, automata groups have decidable word problem.

## Depends on

- [Functionally recursive groups and contracting automata groups](functionally-recursive-group.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof encodes a Minsky machine (a finite automaton with two counters valued in $\mathbb{N}$) in a transducer $\Phi_M$: the counters are stored in the input word, the machine's moves are simulated by the recursive action, and whether a chosen generator is trivial becomes equivalent to a halting question for the machine. Since the halting problem for Minsky machines is undecidable (Proposition 2.2 of the source), so is the word problem for the family of groups $\langle \Phi_M \rangle$.

## Sources

- Laurent Bartholdi and Ivan Mitrofanov, "The word and order problems for self-similar and automata groups", *Groups, Geometry, and Dynamics* 14(2):705–728, 2020, doi:[10.4171/GGD/560](https://doi.org/10.4171/GGD/560). Numbering of the version read, arXiv:1710.10109v4: Theorems A, A′ and A″, and Section 2 (Proposition 2.2 and the proofs in Sections 2.1–2.3).

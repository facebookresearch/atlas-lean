# Syntactic verification conditions are sufficient

Let $\{P\}\, C\, \{Q\}$ be a properly annotated specification and $c$ the command $C$ with its annotations removed. Hoare derivability uses the substitution assignment axiom, sequencing, conditional and invariant-while rules, and consequence with implications proved in the assertion proof system $\mathcal{T}$.

1. If every [syntactic verification condition](syntactic-verification-conditions.md) of $\{P\}\, C\, \{Q\}$ is provable in the proof system $\mathcal{T}$ for the assertion language, then $\{P\}\, c\, \{Q\}$ is derivable in the Hoare logic over $\mathcal{T}$.
2. Consequently, if $\mathcal{T}$ is sound relative to an interpretation $\mathcal{I}$ and every verification condition is provable in $\mathcal{T}$, then every terminating execution of $c$ from a state satisfying $P$ ends in a state satisfying $Q$.

For a sound assertion proof system that proves propositional tautologies, the converse of part 1 fails: the conditions of $\{\mathrm{true}\}\ \mathtt{while}\ \mathrm{false}\ \mathtt{do}\ \{\mathrm{false}\}\, X := 0\ \{\mathrm{true}\}$ are not provable, although the unannotated triple is derivable.

## Depends on

- [Syntactic verification conditions](syntactic-verification-conditions.md)

## Proof depends on

- [Syntactic verification conditions](syntactic-verification-conditions.md)
- [Soundness of Hoare logic over a first-order assertion language](soundness-of-hoare-logic-over-a-first-order-assertion-language.md)

## Sources

- M. Gordon, *Background reading on Hoare Logic*, University of Cambridge Computer Laboratory, 2016, <https://www.cl.cam.ac.uk/archive/mjcg/HL/Notes/Notes.pdf>: Section 3.5 (part 1, by induction on the command, with the non-necessity example).
- S. A. Cook, "Soundness and completeness of an axiom system for program verification", *SIAM Journal on Computing* 7(1):70–90, 1978, <http://www.cs.utoronto.ca/~sacook/homepage/soundness.pdf>: Section 5, Theorem 1 and its Corollary (part 2, applied to the derivation of part 1).

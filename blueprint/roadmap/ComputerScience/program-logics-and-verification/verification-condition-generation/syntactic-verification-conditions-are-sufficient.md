# Syntactic verification conditions are sufficient

Let $\{P\}\, C\, \{Q\}$ be a properly annotated specification and $c$ the command $C$ with its annotations removed. Let $\mathcal{T}$ be a proof system for the assertion language. Derivability in the Hoare logic over $\mathcal{T}$ uses the assignment axiom $\{Q[E/V]\}\ V := E\ \{Q\}$ with capture-avoiding substitution, the sequencing rule, the conditional rule, the while rule with an invariant, and the rule of consequence, whose implications between assertions must be provable in $\mathcal{T}$.

**Theorem.** If every [syntactic verification condition](syntactic-verification-conditions.md) of $\{P\}\, C\, \{Q\}$ is provable in $\mathcal{T}$, then $\{P\}\, c\, \{Q\}$ is derivable in the Hoare logic over $\mathcal{T}$.

The theorem concludes derivability only. If $\mathcal{T}$ is moreover sound relative to an interpretation, the [soundness of Hoare logic over a first-order assertion language](soundness-of-hoare-logic-over-a-first-order-assertion-language.md), applied to the derivation, gives the semantic reading: every terminating execution of $c$ from a state satisfying $P$ ends in a state satisfying $Q$. That reading is an application of the soundness theorem, not a further claim of this page.

The converse fails. For a sound assertion proof system that proves propositional tautologies, the conditions of $\{\mathrm{true}\}\ \mathtt{while}\ \mathrm{false}\ \mathtt{do}\ \{\mathrm{false}\}\, X := 0\ \{\mathrm{true}\}$ are not provable, although the unannotated triple is derivable.

## Depends on

- [Syntactic verification conditions](syntactic-verification-conditions.md)

## Proof depends on

- [Syntactic verification conditions](syntactic-verification-conditions.md)

The proof is by induction on the annotated command, using the axiom and rules listed above.

## Sources

- M. Gordon, *Background reading on Hoare Logic*, University of Cambridge Computer Laboratory, 2016, <https://www.cl.cam.ac.uk/archive/mjcg/HL/Notes/Notes.pdf>: Section 3.5 (the theorem, proved by induction on the command, and the non-necessity example).
- S. A. Cook, "Soundness and completeness of an axiom system for program verification", *SIAM Journal on Computing* 7(1):70–90, 1978, <http://www.cs.utoronto.ca/~sacook/homepage/soundness.pdf>: Section 5, Theorem 1 and its Corollary, which start from a derivable triple; cited only for the semantic reading above.

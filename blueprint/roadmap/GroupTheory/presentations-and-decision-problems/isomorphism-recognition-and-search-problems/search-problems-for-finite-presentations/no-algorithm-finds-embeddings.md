# No algorithm finds embeddings between finitely presented groups

No algorithm takes finite presentations $P$ and $Q$ such that the group of $P$ embeds in the group of $Q$, and outputs an explicit map on generators that extends to such an embedding.

There is no algorithm that, on input of two finite presentations $P = \langle X \mid R \rangle$ and $Q = \langle Y \mid S \rangle$ such that $\overline{P}$ embeds in $\overline{Q}$, outputs a map $\theta\colon X \to W(Y)$ that extends to an injective homomorphism $\overline{\theta}\colon \overline{P} \to \overline{Q}$ (Theorem 6.6 of the source).

Here $W(X)$ is the set of words over $X \cup X^{-1}$, a finite presentation $P = \langle X \mid R \rangle$ has finite sets $X$ and $R \subseteq W(X)$, and $\overline{P}$ is the group it presents. An algorithm for such a search problem need only succeed on the inputs satisfying the stated promise; the statements say that no algorithm succeeds on all of them.

## Depends on

- [Group](../../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof uses torsion: Lemma 6.5 shows that no algorithm, given a finite presentation of a group with torsion and an integer $n$ that is the order of some non-trivial torsion element, outputs a word representing a non-trivial torsion element. A cyclic group $\langle t \mid t^n \rangle$ embeds in a group exactly when the group has an element of order $n$, so an embedding produced by an algorithm as in the theorem would produce such a word.

## Sources

- M. Chiodo, "Finding non-trivial elements and splittings in groups", Journal of Algebra 331 (2011), no. 1, 271–284, https://doi.org/10.1016/j.jalgebra.2010.12.013; arXiv:1002.2786v3 (Lemma 6.5 and Theorem 6.6 of arXiv:1002.2786v3).

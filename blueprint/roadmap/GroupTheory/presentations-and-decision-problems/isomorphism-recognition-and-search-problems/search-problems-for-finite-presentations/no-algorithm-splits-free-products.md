# No algorithm splits a finitely presented free product into non-trivial factors

No algorithm takes a finite presentation of a group that is a free product of two non-trivial finitely presented groups and outputs finite presentations of two non-trivial groups whose free product is that group.

There is no algorithm that, on input of a finite presentation $P$ of a group that is a free product of two non-trivial finitely presented groups, outputs two finite presentations $P_1, P_2$ that present non-trivial groups with $\overline{P_1} * \overline{P_2} \cong \overline{P}$ (Theorem 5.5 of the source).

Here $W(X)$ is the set of words over $X \cup X^{-1}$, a finite presentation $P = \langle X \mid R \rangle$ has finite sets $X$ and $R \subseteq W(X)$, and $\overline{P}$ is the group it presents. An algorithm for such a search problem need only succeed on the inputs satisfying the stated promise; the statements say that no algorithm succeeds on all of them.

As a consequence, Stallings' theorem that a finitely generated group with more than one end splits over a finite subgroup cannot be made algorithmic: there is no algorithm that, given a finite presentation of a group with more than one end, rewrites it as an amalgamated product or HNN extension over a finite subgroup (Corollary 7.2). Similarly, splitting a closed 4-manifold that is a connected sum of two non-simply connected manifolds cannot be done algorithmically from a triangulation.

## Depends on

- [Group](../../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Lemma 5.4: no algorithm, given a presentation $\Pi_{n,a} * \Pi_{n,b} * \Pi_{n,c}$ in which at most one of $a, b, c$ lies in $W_n$, outputs two finite presentations of non-trivial groups whose free product is isomorphic to the given group. The proof shows that such a splitting would single out factors that are non-trivial, contradicting the recursive inseparability arguments of Section 4.

## Sources

- M. Chiodo, "Finding non-trivial elements and splittings in groups", Journal of Algebra 331 (2011), no. 1, 271–284, https://doi.org/10.1016/j.jalgebra.2010.12.013; arXiv:1002.2786v3 (Lemma 5.4, Theorem 5.5, Corollary 7.2 and Corollary 7.4 of arXiv:1002.2786v3).

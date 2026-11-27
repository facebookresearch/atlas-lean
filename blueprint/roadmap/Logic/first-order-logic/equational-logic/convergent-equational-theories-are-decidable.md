# Convergent sets of equations decide their equational theory

Let $E$ be a set of equations that is convergent, that is, $\to_E$ is terminating and [confluent](../term-rewriting/confluence-of-a-relation.md). Then every term $t$ has a unique normal form $t{\downarrow_E}$ with respect to $\to_E$, and for all terms $s, t$:

$$s \approx_E t \iff s \leftrightarrow_E^* t \iff s{\downarrow_E} = t{\downarrow_E}.$$

If $E$ is moreover finite, then $\approx_E$ is decidable: compute the two normal forms and compare them.

**Proof.** Termination gives normal forms; confluence makes them unique, since two normal forms of one term are joinable and hence equal. The first equivalence is Birkhoff's theorem. By the Church–Rosser property, $s \leftrightarrow_E^* t$ makes $s$ and $t$ joinable, and joinable terms have the same normal form; the converse is immediate. For finite $E$ the rewrite steps from a term can be enumerated, and termination bounds the search.

## Depends on

- [Equational consequence and E-algebras](equational-consequence-and-e-algebras.md)
- [Confluence of a relation](../term-rewriting/confluence-of-a-relation.md)

## Proof depends on

- [Birkhoff's completeness theorem for equational logic](birkhoff-s-completeness-theorem.md)
- [The Church–Rosser property is equivalent to confluence](../term-rewriting/church-rosser-property-and-confluence.md)
- [Terminating relations are normalizing](../term-rewriting/terminating-relations-are-normalizing.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.3, Lemma 4.8, Corollary 4.9 and Corollaries 4.12 and 4.13, pp. 110–111.

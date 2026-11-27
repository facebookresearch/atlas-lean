# Unrestricted determinacy of conjunctive queries is undecidable

No algorithm decides, given finitely many conjunctive views and a conjunctive query, whether the views determine the query over all structures, finite or infinite; this settled a problem open since 1985.

**Theorem.** The conjunctive query determinacy problem, unrestricted version, is undecidable. Input: a finite set $\mathcal{Q} = \{Q_1, \dots, Q_k\}$ of conjunctive queries and a conjunctive query $Q_0$ over a common relational signature, which may contain constants. Question: does $\mathcal{Q}$ [determine](determinacy-of-a-query-by-views.md) $Q_0$, that is, do all relational structures $\mathbb{D}_1, \mathbb{D}_2$, finite or infinite, with $Q(\mathbb{D}_1) = Q(\mathbb{D}_2)$ for every $Q \in \mathcal{Q}$ satisfy $Q_0(\mathbb{D}_1) = Q_0(\mathbb{D}_2)$?

## Depends on

- [Determinacy of a query by views](determinacy-of-a-query-by-views.md)
- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)

## Proof depends on

None.

## Expansion

Determinacy is reformulated through the chase: with a green and a red copy of the signature, $\mathcal{Q}$ determines $Q_0$ iff the red copy of $Q_0$ holds in the chase of the green canonical structure of $Q_0$ by the tuple-generating dependencies that recolor each view from green to red and back. The proof shows that this green-red chase can simulate the rewriting of a suitable Thue system ("friendly" Thue systems, a variant of the semigroup word problem), using "spiders", star-shaped queries whose legs carry colors, to encode words; then $\mathcal{Q}$ determines $Q_0$ iff a word rewrites to a target word, which is undecidable. The finite version, where $\mathbb{D}_1, \mathbb{D}_2$ range over finite structures only, was left open by this proof and later shown undecidable by the same authors ([finite determinacy of conjunctive queries is undecidable](finite-determinacy-of-cqs-is-undecidable.md)). Determinacy is undecidable earlier for unions of conjunctive queries, and for conjunctive views with a first-order query (Nash, Segoufin and Vianu).

## Sources

- Tomasz Gogacz and Jerzy Marcinkowski, "The hunt for a red spider: conjunctive query determinacy is undecidable", *Proceedings of the 30th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2015)*, 281–292, 2015, <https://doi.org/10.1109/LICS.2015.35>; read as arXiv:1501.01817v2, <https://arxiv.org/abs/1501.01817v2>: Theorem 1, the definitions of Section 1 and Section 2.1, and the outline of the proof (green-red TGDs, spiders and friendly Thue systems) of that version.

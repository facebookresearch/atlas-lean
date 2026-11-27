# Finite completeness of the inclusion dependency rules

Over a finite schema and a countably infinite value domain, let $F$ be a set of INDs and $\sigma$ an IND. If every finite instance satisfying $F$ satisfies $\sigma$, there is a finite derivation of $\sigma$ from $F$. Each line is a hypothesis, a reflexive inclusion (IND1), a common injective selection and reordering of an earlier inclusion's positions (IND2), or a transitive composition of two earlier inclusions with identical middle projections (IND3).

To see why finite instances suffice, start with one source row for $\sigma$: give its $m$ selected positions distinct markers and all unselected positions a default value different from the markers. Leave all other extents empty. For a missing witness to an IND of $F$, copy the required coordinates into a new target row and use the default elsewhere. There are only finitely many possible rows over these $m+1$ values, so adding missing witnesses stops at a finite instance satisfying $F$. By induction on insertions, any ordered selection of marker positions in a generated row has a derivation of its inclusion from the corresponding positions of the seed: use IND1 at the seed, then IND2 and IND3 at a copied row. A target witness for the seed at termination therefore yields a derivation of $\sigma$.

## Depends on

- [Syntax of an inclusion dependency](../ind.md)
- [Finite implication of dependencies](../finitely-implies.md)

## Proof depends on

- [A joint witness for a projected row](../holds-in-iff-exists-row.md)
- [Finite extents and finite active domain](../is-finite-iff-finite-active-domain.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, [*Foundations of Databases*](https://webdam.di.ens.fr/Alice/pdfs/all.pdf), Addison-Wesley, 1995, Theorem 9.1.3 and its completeness proof, pp. 193–195; the proof of Theorem 9.2.3, p. 199, explicitly uses this finite interpretation.

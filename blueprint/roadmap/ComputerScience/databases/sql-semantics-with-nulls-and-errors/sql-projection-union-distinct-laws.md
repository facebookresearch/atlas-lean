# Projection, UNION ALL, join and DISTINCT laws

Under strict bag semantics: projections fuse by substitution when the inner projection is safe, and $\mathsf{SELECT}\ \ast$ is the identity; $\mathsf{WHERE}$ and $\mathsf{SELECT}$ lists distribute over $\mathsf{UNION\ ALL}$, which is associative (ordered equivalence) and commutative only up to bag equivalence; inner joins are commutative up to bag equivalence after exchanging the column blocks of the predicate and the result; and $\mathsf{DISTINCT}$ is idempotent, absorbs $q\ \mathsf{UNION\ ALL}\ q$, and commutes with $\mathsf{WHERE}$. All laws except the two commutativity laws are ordered equivalences.

## Depends on

- [Three levels of SQL query equivalence and their congruence](sql-query-equivalence-levels.md)

## Proof depends on

- [Type soundness and safety for SQL expressions](sql-type-soundness.md)

## Sources

- P. Guagliardo and L. Libkin, "A Formal Semantics of SQL Queries, Its Validation, and Applications", Proceedings of the VLDB Endowment 11(1), 2017.
- S. Abiteboul, R. Hull and V. Vianu, "Foundations of Databases", Addison-Wesley, 1995.

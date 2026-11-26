# Finite and unrestricted implication of functional and inclusion dependencies

Fix a countably infinite value domain. Let $F$ be a set of [schema dependencies](dependency.md) and $\sigma$ a dependency on the same schema. Compare [finite implication](finitely-implies.md) and [unrestricted implication](implies.md), using the same notion of [satisfaction by an instance](holds-in-2.md) in both cases.

When the hypotheses and conclusion are all functional dependencies, $F$ finitely implies $\sigma$ if and only if it implies $\sigma$ without restriction. The same holds when they are all inclusion dependencies. When the two kinds are allowed together, there exist $F$ and $\sigma$ such that every finite instance satisfying $F$ satisfies $\sigma$, but some infinite instance satisfies $F$ and violates $\sigma$. For finite input sets of such dependencies, both the finite and the unrestricted implication problems are undecidable.

## Depends on

- [Functional and inclusion dependencies on a schema](dependency.md)
- [Satisfaction of a schema dependency](holds-in-2.md)
- [Finite implication of dependencies](finitely-implies.md)
- [Unrestricted implication of dependencies](implies.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, [*Foundations of Databases*](https://webdam.di.ens.fr/Alice/pdfs/all.pdf), Addison-Wesley, 1995, §9.2: Theorems 9.2.2 (mixed dependencies can separate the two implications), 9.2.3 (coincidence for each kind alone), and 9.2.4 (undecidability for mixed dependencies).

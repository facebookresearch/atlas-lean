# Fourth normal form

Let $U$ be a finite set of attributes and $\Sigma$ a set of functional, multivalued and join dependencies over $U$; the
conditions below only test the functional and multivalued dependencies that $\Sigma$ implies, so they apply unchanged when
$\Sigma$ contains join dependencies. The schema
$(U, \Sigma)$ is in *fourth normal form* (4NF) when

1. whenever $\Sigma \models X \to Y$ and $Y \not\subseteq X$, then $\Sigma \models X \to U$; and
2. whenever $\Sigma \models X \twoheadrightarrow Y$, $Y \not\subseteq X$ and $X \cup Y \ne U$, then $\Sigma \models X \to U$.

The condition $X \cup Y \ne U$ excludes the trivial dependencies $X \twoheadrightarrow U \setminus X$, which every relation
satisfies; without it, every proper subset $X$ of $U$ would have to be a superkey, and the schema over $\{A, B\}$ with the
single dependency $A \to B$ would fail the definition through $B \twoheadrightarrow A$.

A database schema is in 4NF when each of its relation schemas is.

## Depends on

- [Join dependencies and multivalued dependencies](join-dependencies-and-multivalued-dependencies.md)
- [Functional dependency](../../functional-dependencies/fd.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Definition 11.2.2 (p. 252); its condition (b) as printed omits $X \cup Y \ne U$, which is restored here as in Fagin's definition, consistent with the book's Definition 8.3.2 (p. 170) and Exercise 11.7.
- R. Fagin, "Multivalued dependencies and a new normal form for relational databases", *ACM Trans. Database Syst.* 2(3) (1977) 262–278.

# Fourth normal form

Let $U$ be a finite set of attributes and $\Sigma$ a set of functional and multivalued dependencies over $U$. The schema
$(U, \Sigma)$ is in *fourth normal form* (4NF) when

1. whenever $\Sigma \models X \to Y$ and $Y \not\subseteq X$, then $\Sigma \models X \to U$; and
2. whenever $\Sigma \models X \twoheadrightarrow Y$ and $Y \not\subseteq X$, then $\Sigma \models X \to U$.

A database schema is in 4NF when each of its relation schemas is.

## Depends on

- [Join dependencies and multivalued dependencies](join-dependencies-and-multivalued-dependencies.md)
- [Functional dependency](../../functional-dependencies/fd.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Definition 11.2.2 (p. 252).
- R. Fagin, "Multivalued dependencies and a new normal form for relational databases", *ACM Trans. Database Syst.* 2(3) (1977) 262–278.

# Join dependencies and multivalued dependencies

Let $U$ be a finite set of attributes. A *join dependency* over $U$ is an expression $\bowtie[X_1, \dots, X_n]$ with
$X_1, \dots, X_n \subseteq U$ and $X_1 \cup \dots \cup X_n = U$; a relation $I$ over $U$ satisfies it when
$I = \pi_{X_1}(I) \bowtie \dots \bowtie \pi_{X_n}(I)$. It is $n$-ary if it has $n$ components. A *multivalued dependency*
over $U$ is an expression $X \twoheadrightarrow Y$ with $X, Y \subseteq U$; a relation $I$ over $U$ satisfies it when it
satisfies the binary join dependency $\bowtie[XY, X(U \setminus Y)]$. Thus the binary join dependencies are exactly the
multivalued dependencies.

## Depends on

- [Relational algebra queries](../../relational-algebra/expr.md)
- [Join of the projections of a relation](../../lossless-decomposition-and-normal-forms/join-projections.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Definitions 8.3.1 and 8.3.2 (p. 170).
- R. Fagin, "Multivalued dependencies and a new normal form for relational databases", *ACM Trans. Database Syst.* 2(3) (1977) 262–278.

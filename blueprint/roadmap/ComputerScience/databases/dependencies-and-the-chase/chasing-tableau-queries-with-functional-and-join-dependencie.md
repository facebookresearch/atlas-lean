# Chasing tableau queries with functional and join dependencies

Let $R$ be a relation schema, $F$ a set of functional and join dependencies over $R$, and $(T,t)$ a tableau query over $R$ without constants. Every chasing sequence of
$(T,t)$ by $F$ terminates, and all terminal chasing sequences yield the same result up to renaming of
variables (the chase is Church–Rosser). Moreover, $F$ logically implies a dependency $\sigma$ if and only if
chasing the tableau associated with $\sigma$ by $F$ produces the conclusion of $\sigma$: the cells that are not distinguished hold fresh variables, and a
distinguished variable stays distinguished when it is identified with another; for a functional dependency
$X \to A$, chasing the two-row tableau that agrees exactly on $X$ identifies its two $A$-entries; for a join dependency
$\bowtie[R_1, \dots, R_k]$, chasing the tableau with one row per $R_i$, distinguished exactly on $R_i$, yields a row that is
distinguished everywhere. This yields the
tableau test for lossless joins.

## Depends on

- [Join dependencies and multivalued dependencies](multivalued-and-join-dependencies/join-dependencies-and-multivalued-dependencies.md)
- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Functional dependency](../functional-dependencies/fd.md)
- [A functional dependency holds in a relation](../functional-dependencies/holds-in.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995 (authors' web edition), the restriction to tableau queries with no constants at the start of Section 8.4 (p. 175), Lemma 8.4.4, Theorem 8.4.12 and Theorem 8.4.18. <http://webdam.inria.fr/Alice/pdfs/all.pdf>

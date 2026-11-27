# Chasing tableau queries with functional and join dependencies

Let $R$ be a relation schema, $F$ a set of functional and join dependencies over $R$, and $(T,t)$ a tableau query over $R$. Every chasing sequence of
$(T,t)$ by $F$ terminates, and all terminal chasing sequences yield the same result up to renaming of
variables (the chase is Church–Rosser). Moreover, $F$ logically implies a dependency $\sigma$ if and only if
chasing the tableau associated with $\sigma$ by $F$ produces the conclusion of $\sigma$. This yields the
tableau test for lossless joins.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Multivalued and join dependencies; 4NF.
- Statement prerequisite: Conjunctive queries, answers and canonical databases.

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995 (authors' web edition), Lemma 8.4.4, Theorem 8.4.12 and Theorem 8.4.18. <http://webdam.inria.fr/Alice/pdfs/all.pdf>

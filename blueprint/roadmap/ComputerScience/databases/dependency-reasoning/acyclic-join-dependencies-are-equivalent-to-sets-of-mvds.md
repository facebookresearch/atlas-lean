# A join dependency is acyclic if and only if it is equivalent to a set of multivalued dependencies

A join dependency $\bowtie[X_1, \dots, X_n]$ is acyclic when the hypergraph with hyperedges $X_1, \dots, X_n$ is
acyclic. A join dependency $\sigma$ is acyclic if and only if some set $F$ of multivalued dependencies is equivalent
to $\sigma$ (every relation satisfies $\sigma$ exactly when it satisfies $F$). Such a set cannot be read off an arbitrary
order of ear removals: for the join path $AB, BC, CD$ the removal order $AB, CD, BC$ gives the cuts
$AB \mid BCD$ and $ABCD \mid BC$, and the relation $\{0000, 0101\}$ over $ABCD$ satisfies both binary joins but not
$\bowtie[AB, BC, CD]$, whose join of projections also contains $0001$.

## Depends on

- [Multivalued and join dependencies; 4NF](../dependencies-and-the-chase/multivalued-and-join-dependencies-4nf.md)
- [Characterizations of acyclic database schemas](../join-processing/characterizations-of-acyclic-database-schemas.md)

## Proof depends on

- [Chasing tableau queries with functional and join dependencies](../dependencies-and-the-chase/chasing-tableau-queries-with-functional-and-join-dependencie.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, the definition of acyclic join dependencies and Theorem 8.4.15 (pp. 182–183).

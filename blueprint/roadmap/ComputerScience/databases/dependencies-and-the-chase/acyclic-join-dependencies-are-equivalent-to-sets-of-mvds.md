# A join dependency is acyclic if and only if it is equivalent to a set of multivalued dependencies

A join dependency $\bowtie[X_1, \dots, X_n]$ is acyclic when the hypergraph with hyperedges $X_1, \dots, X_n$ is
acyclic. A join dependency $\sigma$ is acyclic if and only if some set $F$ of multivalued dependencies is equivalent
to $\sigma$ (every relation satisfies $\sigma$ exactly when it satisfies $F$). If $X_1, \dots, X_n$ is the order in which
the GYO algorithm removes the hyperedges as ears, one such set is
$\{(P_i \cap Q_i) \twoheadrightarrow Q_i : 1 \le i < n\}$ with $P_i = X_1 \cup \cdots \cup X_i$ and
$Q_i = X_{i+1} \cup \cdots \cup X_n$.

## Depends on

- [Multivalued and join dependencies; 4NF](multivalued-and-join-dependencies-4nf.md)
- [Characterizations of acyclic database schemas](../join-processing/characterizations-of-acyclic-database-schemas.md)

## Proof depends on

- [Chasing tableau queries with functional and join dependencies](chasing-tableau-queries-with-functional-and-join-dependencie.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, the definition of acyclic join dependencies and Theorem 8.4.15 with its proof (pp. 182–183).

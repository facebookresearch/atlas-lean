# The LCA reconciliation is optimal for duplication, loss and deep coalescence costs

Let $G$ be a rooted binary gene tree and $S$ a rooted binary species tree, with each leaf of $G$ labelled by a leaf of $S$. A reconciliation is a map $f : V(G) \to V(S)$ that is leaf-preserving and order-preserving ($u \le v$ in $G$ implies $f(u) \le f(v)$ in $S$). Reconciliations are partially ordered by $f' \preceq f$ if $f'(v) \le f(v)$ for every vertex $v$, and the least-common-ancestor (LCA) reconciliation $M$ satisfies $M \preceq f$ for every reconciliation $f$. Wu and Zhang (2011, Theorem 2) prove that if $f' \preceq f$ are distinct, then the gene duplication cost does not increase from $f$ to $f'$, while the gene loss and deep coalescence costs strictly decrease. Hence (Corollary 4) $M$ has the minimum gene duplication cost and is the unique reconciliation with the minimum gene loss cost and the unique one with the minimum deep coalescence cost; the first two statements are earlier results that they cite. Duplication-optimal reconciliations need not be unique: there is a reconciliation $M^*$ such that $f$ has the minimum duplication cost if and only if $M \preceq f \preceq M^*$ (Theorem 5). They also give algorithms enumerating the reconciliations within a given margin of the optimum for each cost by traversing a tree structure on the space of reconciliations rooted at $M$.

## Expansion

1. Definitions: binary gene and species trees, reconciliations as leaf- and order-preserving maps, the LCA map, and the duplication, loss and deep coalescence costs.
2. The partial order on reconciliations and the LCA map as its minimum, by a bottom-up traversal.
3. Theorem 2: comparison of the three costs along the partial order, with the vertexwise duplication indicators $\delta_f(u)$.
4. Corollary 4, and the construction of $M^*$ with Theorem 5.
5. The enumeration algorithms for nearly optimal reconciliations and their running times, as separate statements.

## Sources

- T. Wu and L. Zhang, Structural properties of the reconciliation space and their applications in enumerating nearly-optimal reconciliations between a gene tree and a species tree, BMC Bioinformatics 12 (Suppl. 9) (2011), S7, Theorem 2, Corollary 4 and Theorem 5. <https://doi.org/10.1186/1471-2105-12-s9-s7>

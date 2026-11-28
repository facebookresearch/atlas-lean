# The duplication-optimal reconciliations form an interval above the LCA reconciliation

Let $G$ be a rooted binary gene tree and $S$ a rooted binary species tree, with each leaf of $G$ labelled by a leaf of $S$. A [reconciliation](../../../not-yet-classified/lcareconciliation/is-reconciliation.md) is a map $f : V(G) \to V(S)$ that is leaf-preserving and order-preserving, and reconciliations are partially ordered by $f' \preceq f$ if $f'(v) \le f(v)$ for every vertex $v$; the LCA reconciliation $M$ is the least element. By [the optimality of the LCA reconciliation](../../../not-yet-classified/lcareconciliation/lca-optimal.md) (Wu and Zhang 2011, Corollary 4), $M$ has the minimum [gene duplication cost](../../../not-yet-classified/lcareconciliation/gd.md) $\mathrm{gd}$, but duplication-optimal reconciliations need not be unique. Wu and Zhang (2011, Theorem 5) prove that there is a reconciliation $M^*$ such that a reconciliation $f$ has the minimum gene duplication cost if and only if $M \preceq f \preceq M^*$.

## Depends on

- [Is Reconciliation](../../../not-yet-classified/lcareconciliation/is-reconciliation.md)
- [Gd](../../../not-yet-classified/lcareconciliation/gd.md)
- [Optimality of the LCA reconciliation](../../../not-yet-classified/lcareconciliation/lca-optimal.md)

## Proof depends on

- [Monotonicity of the costs](../../../not-yet-classified/lcareconciliation/costs-lt-of-le.md)

## Expansion

1. The construction of $M^*$ and the proof of Theorem 5 from the monotonicity of the duplication cost along the partial order.
2. The enumeration algorithms for nearly optimal reconciliations and their running times, as separate statements.

## Sources

- T. Wu and L. Zhang, Structural properties of the reconciliation space and their applications in enumerating nearly-optimal reconciliations between a gene tree and a species tree, BMC Bioinformatics 12 (Suppl. 9) (2011), S7, Theorem 2, Corollary 4 and Theorem 5. <https://doi.org/10.1186/1471-2105-12-s9-s7>

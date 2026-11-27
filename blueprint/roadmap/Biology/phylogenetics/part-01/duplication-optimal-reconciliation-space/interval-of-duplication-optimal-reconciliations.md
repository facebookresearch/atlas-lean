# Interval of duplication-optimal reconciliations

Let $G$ and $S$ be rooted binary gene and species trees, with gene leaves labelled by species. A **reconciliation** is a map $f : V(G) \to V(S)$ that sends each leaf to its species and is order-preserving ($f(u) \le f(p(u))$ in the ancestor order of $S$). For an internal $u$ with children $u_1, u_2$, $u$ is a **duplication** under $f$ ($\delta_f(u) = 1$) iff $f(u) \in \{f(u_1), f(u_2)\}$ or $\mathrm{lca}(f(u_1), f(u_2)) < f(u)$; $\mathrm{gd}(f) = \sum_u \delta_f(u)$. Write $f' \preceq f$ if $f'(u) \le f(u)$ for all $u$; the LCA reconciliation $M(u) = \mathrm{lca}$ of the species below $u$ is the least reconciliation.

**Facts.** If $\delta_f(u) = 0$ then $f(u) = M(u)$ and the leaf sets below $f(u_1)$ and $f(u_2)$ are disjoint; if $f(u) > M(u)$ then $\delta_f(u) = 1$. For $f' \preceq f$, $\delta_{f'}(u) \le \delta_f(u)$ at every vertex, with equality everywhere iff $\mathrm{gd}(f') = \mathrm{gd}(f)$.

Define $M^*$ by $M^*(u) = M(u)$ if $\delta_M(u) = 0$; $M^*(r(G)) = r(S)$ if the root is a duplication; and otherwise, for a duplication $u$ with parent already mapped, $M^*(u) = M^*(p(u))$ if $p(u)$ is a duplication ($\delta_M(p(u)) = 1$), and $M^*(u)$ is the largest vertex $s$ of $S$ with $M(u) \le s < M^*(p(u))$ if $p(u)$ is a speciation.

**Theorem.** A reconciliation $f$ has minimum duplication cost if and only if

$$M \preceq f \preceq M^* ,$$

so $M^*$ is the unique maximal duplication-optimal reconciliation and the duplication-optimal reconciliations form an interval of the reconciliation poset.

**Enumeration.** The nearest-mapping-change operator $f \mapsto f[u]$ (moving $f(u)$ one step up, allowed when $f(u) < f(p(u))$) organizes all reconciliations into a tree rooted at $M$, and those with $\mathrm{gd}(f) \le \mathrm{gd}(M) + \varepsilon$ form a subtree; they can be listed in $O(|V(G)|\cdot|\Gamma_\varepsilon|)$ time plus preprocessing, where $\Gamma_\varepsilon$ is the set listed.

## Depends on

- [Monotonicity of the costs](../../../not-yet-classified/lcareconciliation/costs-lt-of-le.md)
- [Optimality of the LCA reconciliation](../../../not-yet-classified/lcareconciliation/lca-optimal.md)

## Expansion

Since every reconciliation lies above $M$ and duplications can only be added when moving up, $f$ is optimal iff $\delta_f = \delta_M$ vertexwise. At a speciation node of $M$ the image is forced; below a speciation node $u_0$, a duplication child $u$ can be lifted as far as the child of $M(u_0)$ on the path to $M(u)$ without disturbing the speciation at $u_0$, and no further; below a duplication node, a duplication child may be lifted up to its parent's image, since the parent stays a duplication; at the root, duplications may be lifted to $r(S)$. Induction from the root downward shows every optimal $f$ satisfies $f \le M^*$ and that $M^*$ itself creates no new duplication. Unlike duplication cost, the loss and deep-coalescence costs are uniquely minimized by $M$.

## Sources

- T. Wu and L. Zhang, "Structural properties of the reconciliation space and their applications in enumerating nearly-optimal reconciliations between a gene tree and a species tree", BMC Bioinformatics 12 (Suppl 9) (2011), S7, Lemma 1, Theorem 2, Corollary 4, Theorem 5 and the enumeration algorithm, <https://doi.org/10.1186/1471-2105-12-s9-s7>, PMCID: PMC3283320.

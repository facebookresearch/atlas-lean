# Edge contraction preserves least resolved trees of best match graphs

**Setting.** A *leaf-colored tree* $(T,\sigma)$ is a rooted tree with a coloring $\sigma$ of its leaves (genes colored by species). A leaf $y$ is a *best match* of $x$ if $\sigma(y)\ne\sigma(x)$ and $\mathrm{lca}_T(x,y)\preceq_T\mathrm{lca}_T(x,y')$ for every leaf $y'$ with $\sigma(y')=\sigma(y)$. The *best match graph* $G(T,\sigma)$ has the leaves as vertices and an arc $(x,y)$ whenever $y$ is a best match of $x$. A tree is *least resolved* if no nonempty set $A$ of edges can be contracted without changing its best match graph. Every best match graph is explained by a unique least resolved tree (LRT), obtained from any explaining tree by contracting its redundant edges; contracting inner edges never removes arcs, $G(T,\sigma)\subseteq G(T_A,\sigma)$.

**Theorem.** Let $(T,\sigma)$ be least resolved and $A$ a set of inner edges of $T$.

1. The contracted tree $(T_A,\sigma)$ is again least resolved.
2. If $A\ne\emptyset$, then $G(T,\sigma)\subsetneq G(T_A,\sigma)$.
3. Distinct inner edges $e\ne e'$ give distinct graphs $G(T_e,\sigma)\ne G(T_{e'},\sigma)$.

So the LRTs are closed under contraction of inner edges, and contraction of $A$ strictly enlarges the best match graph.

## Expansion

An inner edge $uv$ ($v$ a child of $u$) is non-redundant exactly when some arc $(a,b)$ of the best match graph has $\mathrm{lca}(a,b)=v$ and $\sigma(b)$ occurs among the leaves below $u$ but not below $v$. Contracting a different inner edge $e'$ keeps both the witness arc (arcs are only added by contraction) and the color condition, so $uv$ stays non-redundant. Repeating edge by edge shows $T_A$ has no redundant edge. Items 2 and 3 follow because the LRT of a best match graph is unique, so two different least resolved trees cannot explain the same graph. This closure property is what makes edge contraction a safe operation when correcting a noisy best match graph toward a structurally constrained one.

## Sources

- D. Schaller, M. Geiß, M. Hellmuth, P. F. Stadler, "Arc-completion of 2-colored best match graphs to binary-explainable best match graphs", arXiv:2103.06665 (2021), Propositions 1 and 2, Theorem 1, Corollaries 1 and 2, <https://doi.org/10.48550/arXiv.2103.06665>.

# False-positive reciprocal best matches come from duplications with complementary losses

Let $(T, t, \sigma)$ be a leaf-colored, event-labeled gene tree (event labels $\bullet$ for speciation and $\square$ for duplication on inner vertices), with reciprocal best match graph $G(T, \sigma)$ and orthology relation $\Theta(T, t) = \{xy : t(\mathrm{lca}_T(x, y)) = \bullet\}$. For genes $a, b \in L(T)$ let $v = \mathrm{lca}_T(a, b)$ and let $v_a, v_b$ be the children of $v$ with $a \preceq_T v_a$ and $b \preceq_T v_b$. Write $\sigma(L(T(u)))$ for the set of species represented below $u$.

**Theorem 3.** $ab$ is a false-positive orthology edge, $ab \in E(G(T, \sigma)) \setminus E(\Theta(T, t))$, if and only if

$$t(v) = \square \quad\text{and}\quad \sigma(a), \sigma(b) \in \sigma(L(T(v_a))) \,\triangle\, \sigma(L(T(v_b))),$$

where $\triangle$ is the symmetric set difference. Equivalently, $a$ and $b$ are paralogs separated by a duplication after which the lineage containing $a$ lost every copy in species $\sigma(b)$ and the lineage containing $b$ lost every copy in species $\sigma(a)$.

## Depends on

- [Orthology is contained in the reciprocal best match graph](orthology-is-contained-in-the-reciprocal-best-match-graph.md)

## Expansion

If $t(v) = \square$, then $a$ and $b$ are not orthologs by definition. They are reciprocal best matches exactly when no gene of color $\sigma(b)$ lies below $v_a$ and no gene of color $\sigma(a)$ lies below $v_b$, since such a gene would be a strictly closer competitor; and $\sigma(a) \in \sigma(L(T(v_a)))$, $\sigma(b) \in \sigma(L(T(v_b)))$ trivially, so these two exclusions are the symmetric-difference condition. False positives therefore require complementary losses following a duplication. The paper shows that most such edges can be detected as "good quartets" in the RBMG and corrected; horizontal gene transfer, outside the duplication/loss setting, can also create false negatives.

## Sources

- M. Geiß, M. E. González Laffitte, A. López Sánchez, D. I. Valdivia, M. Hellmuth, M. Hernández Rosales, P. F. Stadler, "Best match graphs and reconciliation of gene trees with species trees", Journal of Mathematical Biology (2020), Theorem 3, <https://doi.org/10.1007/s00285-020-01469-y> (PMC7052050).

# Null moments of the community distance

Let $T$ be a phylogenetic tree with tip set $S$, $|S| = s$, edge weights $w_e$, and path costs $\mathrm{cost}(u,v)$. For tip samples $A, B \subseteq S$ with $|A| = a$, $|B| = b$, the **community distance** is

$$\mathrm{CD}(T, A, B) = \frac{1}{ab}\sum_{u\in A}\sum_{v \in B}\mathrm{cost}(u,v),$$

the two-sample analogue of mean pairwise distance. Let $\mathrm{TC}(T) = \sum_{\{u,v\}\subseteq S}\mathrm{cost}(u,v)$ be the total path cost, $\mathrm{TC}(e)$ the total cost of tip-to-tip paths through edge $e$, and $\mathrm{TC}(u)$ the total cost of paths from tip $u$.

**Theorem.** If $A$ and $B$ are drawn independently and uniformly from the subsets of $S$ of sizes $a$ and $b$, then

$$\mathbb{E}\,\mathrm{CD}(T,a,b) = \frac{2}{s^2}\,\mathrm{TC}(T)$$

(Tsirogiannis and Sandel 2016, Theorem 1), and

$$\operatorname{Var}\mathrm{CD}(T,a,b) = k_1\,\mathrm{TC}(T)^2 + (k_2 - k_1)\sum_{u\in S}\mathrm{TC}(u)^2 + (k_1 - 2k_2 + k_3)\sum_{e} w_e\,\mathrm{TC}(e) - \left(\mathbb{E}\,\mathrm{CD}\right)^2$$

with

$$k_1 = \frac{4(a-1)(b-1)}{ab\,s^2(s-1)^2}, \quad k_2 = \frac{2(a-1)(b-1)}{ab\,s^2(s-1)^2} + \frac{(a-1)+(b-1)}{ab\,s^2(s-1)}, \quad k_3 = \frac{2(a-1)(b-1)}{ab\,s^2(s-1)^2} + \frac{2}{ab\,s^2}$$

(Theorem 2, where the stated expression is $\mathbb{E}[\mathrm{CD}^2] - (\mathbb{E}\,\mathrm{CD})^2$). All three tree sums are computable in $O(s)$ time by tree traversals, which makes the standardized index $\mathrm{NRI}_\beta = (\mathrm{CD} - \mathbb{E}\,\mathrm{CD})/\sqrt{\operatorname{Var}\mathrm{CD}}$ feasible on very large trees.

## Expansion

Write $\mathrm{CD} = \frac{1}{ab}\sum_{\{u,v\}}\mathrm{cost}(u,v)\,[\mathbf 1_{u\in A}\mathbf 1_{v\in B} + \mathbf 1_{v\in A}\mathbf 1_{u\in B}]$. By independence, $\mathbb{E}[\mathbf 1_{u\in A}\mathbf 1_{v \in B}] = ab/s^2$, which gives the mean. The second moment is a double sum over pairs of paths; grouping by whether the two paths share zero, one or two endpoints yields the three tree statistics, and $\sum_{\{u,v\}}\mathrm{cost}(u,v)^2 = \sum_e w_e\,\mathrm{TC}(e)$ because each path cost is a sum of its edge weights. Check: for $s = 2$, $a = b = 1$, the formula gives $\mathbb{E}\,\mathrm{CD} = c/2$ and variance $c^2/4$ for the single path cost $c$, matching direct enumeration.

## Sources

- C. Tsirogiannis and B. Sandel, *Fast computations for measures of phylogenetic beta diversity*, PLoS ONE 11(4) (2016), e0151167, Eq. (1) and Theorems 1–2. <https://doi.org/10.1371/journal.pone.0151167> (PMCID: PMC4824508)

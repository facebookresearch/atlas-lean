# Robust cherry lemma for split systems

Let $X$ be a finite set of at least four taxa and $(A_e)_{e \in E}$ a finite family of subsets of $X$ with weights $w_e > 0$ such that

- every $A_e$ is nonempty;
- for every $e$ there is $e'$ with $A_{e'} = X \setminus A_e$;
- any two members are compatible: $A_e \cap A_{e'} = \emptyset$, $A_e \subseteq A_{e'}$, $A_{e'} \subseteq A_e$ or $A_e \cup A_{e'} = X$;
- every $A_e$ with at least two elements is the disjoint union of two members of the family;
- every singleton $\{z\}$ is a member.

Put $d(x, y) = \frac12 \sum_{e \,:\, A_e \text{ separates } x, y} w_e$, and let $\mu$ satisfy $\mu \le w_e$ for every $e$ with $|A_e| \ge 2$ and $|X \setminus A_e| \ge 2$. Let $D : X \times X \to \mathbb{R}$ be symmetric with $D(x, x) = 0$ and $|D(x, y) - d(x, y)| < \mu/2$ for all distinct $x, y$. If distinct taxa $x, y$ minimize

$$Q(x, y) = (|X| - 2) D(x, y) - \sum_{z} D(x, z) - \sum_{z} D(y, z)$$

over all pairs of distinct taxa, then $\{x, y\} = A_e$ for some $e$ (Atteson 1999; proof after Mihaescu, Levy & Pachter 2009, Theorem 16).

## Sources

- K. Atteson, *The performance of neighbor-joining methods of phylogenetic reconstruction*, Algorithmica 25 (1999), 251–278.
- R. Mihaescu, D. Levy and L. Pachter, *Why neighbor-joining works*, Algorithmica 54 (2009), 1–24; arXiv:cs/0602041, Theorem 16.

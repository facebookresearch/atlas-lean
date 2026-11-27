# Upper bounds on the reticulation number of three or more trees

**Setting.** A rooted binary phylogenetic network on taxa $X$ ($|X| = n$) *displays* a rooted binary phylogenetic tree on $X$ if the tree can be obtained by deleting one incoming arc at each reticulation and suppressing degree-two vertices. For a set $\mathcal{T}$ of trees on $X$, the *reticulation number* $R(\mathcal{T})$ is the minimum, over networks displaying every tree of $\mathcal{T}$, of $\sum_v (\mathrm{indeg}(v) - 1)$ over vertices with in-degree $> 1$.

**Known two-tree facts.** $R(T,T')$ equals the size of a maximum acyclic agreement forest minus one, hence $R(T,T') \le n-2$, with equality for two conjugate caterpillars. If two trees share a rooted agreement subtree on $k$ taxa then $R(T_1,T_2) \le n-k$. For $n \ge 5$, if $T_1$ is not a caterpillar then $R(T_1,T_2) \le n-3$. For $m$ trees with some pair at reticulation number $d$, $R(\mathcal{T}) \le (m-2)(n-2) + d$, so trivially $R(\mathcal{T}) \le (m-1)(n-2)$.

**Theorem (three trees).** For rooted binary trees $T_1, T_2, T_3$ on the same $n$ taxa:
1. some pair among them has a rooted agreement subtree with $\Theta(\log\log n)$ taxa, hence $R(T_1,T_2,T_3) \le 2n - 2 - \Theta(\log\log n)$;
2. if all three are caterpillars, $R(T_1,T_2,T_3) \le 2n - n^{1/3} - 2$;
3. for $n \ge 5$, $R(T_1,T_2,T_3) \le 2n - 5$.

**Theorem (many trees).** For a set $\mathcal{T}$ of $m$ trees on $n$ taxa,

$$R(\mathcal{T}) \le (m-1)(n-2) - \begin{cases} \Theta(m\sqrt m), & m \le n(n-1) + \tfrac16,\\ \Theta(n^3), & \text{otherwise.} \end{cases}$$

## Expansion

The two-tree bound $n-k$ comes from an agreement forest consisting of the common subtree plus $n-k$ singletons. Among three trees, Ramsey-type arguments (via Erdős–Szekeres for caterpillars, where a tree is a permutation of the taxa and agreement subtrees correspond to monotone subsequences) guarantee a pair with a large common subtree; merging that pair first saves the corresponding number of reticulations below the trivial $2(n-2)$, and the third tree is added with at most $n-2$ further reticulations. The constructions are tree-child networks built from lineage taxon strings: for each taxon a common supersequence of the strings it has in the different trees yields a network whose reticulation number is the total excess length, and many trees force many shared subsequences, which is where the $m\sqrt m$ and $n^3$ savings come from.

## Sources

- Yufeng Wu and Louxin Zhang, "Bounding the number of reticulation events for displaying multiple trees in a phylogenetic network", Journal of Computer and System Sciences 152 (2025), 103657, <https://doi.org/10.1016/j.jcss.2025.103657>; numbering as in arXiv:2408.14202: Theorem 2.1, Propositions 2.3–2.4 and 3.1–3.2, Proposition 4.2, Theorem 4.3, Propositions 4.4–4.5 and Theorem 5.1.

# Read-coverage guarantee of greedy maximal satisfiable cluster selection

**Setting.** In the MPSV-CR problem with $k = l = 1$, assume every read of $R$ (with $|R| = m$) is covered by at least one cluster. For a cluster $V$ let $\mathrm{nb}(V) = \{V' : \exists e \in E(\mathrm{CG}),\ V, V' \in e,\ V' \ne V\}$, and let $\Delta = \max_V |\mathrm{nb}(V)|$. The first phase of the Max_Assigned_Reads heuristic starts from $\mathrm{MS} = \emptyset$ and repeatedly adds to $\mathrm{MS}$ a cluster that keeps $\mathrm{MS}$ satisfiable and covers the largest number of reads not yet covered by $\mathrm{MS}$ (possibly zero), until $\mathrm{MS}$ is maximal satisfiable. Let $\mathrm{MR}$ be the set of reads covered by $\mathrm{MS}$. The second phase selects, by greedy set cover, a small subfamily of $\mathrm{MS}$ that still covers $\mathrm{MR}$.

**Theorem 4.2.** $|\mathrm{MR}| \ge \dfrac{m}{\Delta + 1}.$

## Depends on

- [Maximum parsimony structural variation with conflict resolution](maximum-parsimony-structural-variation-with-conflict-resolution.md)

## Expansion

Let $V_1, \dots, V_s$ be the clusters chosen in the first phase, $\mathrm{MR}_i$ the reads covered for the first time by $V_i$, and $\mathrm{UR}_i$ the reads not covered by $V_1, \dots, V_i$ that become impossible to cover in later iterations because of the choice of $V_i$. Such reads are covered only by clusters that the choice of $V_i$ excludes, all of which lie in $\mathrm{nb}(V_i)$; each of these covers at most $|\mathrm{MR}_i|$ still-uncovered reads, otherwise the greedy rule would have preferred it. Hence $|\mathrm{UR}_i| \le \Delta\,|\mathrm{MR}_i|$. Every read is eventually either covered or made uncoverable, so $\sum_i (|\mathrm{UR}_i| + |\mathrm{MR}_i|) = m$, and $m \le (\Delta + 1)\sum_i |\mathrm{MR}_i| = (\Delta + 1)|\mathrm{MR}|$. The second phase inherits the logarithmic approximation guarantee of greedy set cover relative to the best cover of $\mathrm{MR}$ inside $\mathrm{MS}$. Given the $n^{1-\varepsilon}$ inapproximability of the full problem, a guarantee of this degree-dependent form is what one can expect; in practice conflict degrees are small because conflicts are local to a genomic window.

## Sources

- F. Hormozdiari, I. Hajirasouliha, P. Dao, F. Hach, D. Yorukoglu, C. Alkan, E. E. Eichler, S. C. Sahinalp, "Next-generation VariationHunter: combinatorial algorithms for transposon insertion discovery", Bioinformatics 26 (2010) i350–i357, Section 4.3 and Theorem 4.2, <https://doi.org/10.1093/bioinformatics/btq216> (PMC2881400).

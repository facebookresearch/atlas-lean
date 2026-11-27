# Candidate sparsification of canonical pseudoknot recursions

In the Reeder–Giegerich algorithm for a sequence $S$ of length $n$, $W(i,j)$ is the minimum free energy of a structure on $S_i \cdots S_j$ and $K(i,j)$ the best **canonical pseudoknot** spanning $i..j$: two crossing helices with outer pairs $(i,i')$ and $(j',j)$, $i < j' < i' < j$, each stacked to its maximal length $d_{i,i'}$, $d_{j',j}$. Assume the pseudoknot energy depends only on the left ends of its pairs, $\mathrm{PKE}(i, d_{i,i'}, i', j', d_{j',j}, j)$. Then

$$K(i,j) = \min_{i', j'} \mathrm{score}(i,j',i',j),$$

$$\mathrm{score}(i,j',i',j) = \mathrm{PKE}(\cdot) + W(i + d_{i,i'}, j'-1) + W(j' + d_{j',j}, i' - d_{i,i'}) + W(i'+1, j - d_{j',j}).$$

**Candidates.** For $i < j' < i'_1 < i'_2$, say $i'_1$ **dominates** $i'_2$ with respect to $(i, j', d_{j',j})$ if

$$\mathrm{score}_{i'_2}(i,j',i'_2) \ge \mathrm{score}_{i'_2}(i,j',i'_1),$$

where $\mathrm{score}_{c}(i,j',i')$ replaces the last term by $W(i'+1, c)$ (empty for $i' = c$). A non-dominated $i'$ is a **candidate**.

**Lemma.** If $i'_1$ dominates $i'_2$ with respect to $(i,j',d_{j',j})$, then $\mathrm{score}(i,j',i'_1,j) \le \mathrm{score}(i,j',i'_2,j)$ for every $j$. Hence the minimum defining $K(i,j)$ may be restricted to candidates, maintained in lists $L_i(j', d_{j',j})$ while $j$ increases.

The sparsified algorithm runs in $O(n^3 L)$ time instead of $O(n^4)$, where $L = \max_i \sum_{j', d} |L_i(j', d)| \le n$, and keeps $O(n^2)$ space by storing lists only for small stem lengths.

## Depends on

- [Zuker minimum free energy](../../zuker-s-minimum-free-energy-algorithm/zuker-mfe.md)

## Expansion

Add $W(i'_2 + 1, j - d_{j',j})$ to both sides of the domination inequality. The right side then contains $W(i'_1 + 1, i'_2) + W(i'_2 + 1, j - d_{j',j})$, which is at least $W(i'_1 + 1, j - d_{j',j})$ by the triangle inequality $W(x,y) + W(y+1,z) \ge W(x,z)$ (concatenating optimal substructures is a feasible structure on $x..z$). This is the same mechanism as sparsified pseudoknot-free folding, adapted so that dominance is decided once per $(i, j', d_{j',j})$ and reused for all $j$. Empirically the sparsified implementation is two to four times faster on realistic lengths, with the speedup growing roughly linearly in $n$.

## Sources

- M. Möhl, R. Salari, S. Will, R. Backofen and S. C. Sahinalp, "Sparsification of RNA structure prediction including pseudoknots", Algorithms for Molecular Biology 5 (2010), 39, Eqs. (1)–(2), Definition 1, the dominance lemma and complexity analysis, <https://doi.org/10.1186/1748-7188-5-39>, PMCID: PMC3161351.

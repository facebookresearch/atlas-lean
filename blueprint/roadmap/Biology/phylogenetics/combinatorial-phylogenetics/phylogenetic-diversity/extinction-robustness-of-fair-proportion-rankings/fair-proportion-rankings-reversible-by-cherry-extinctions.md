# Fair Proportion rankings reversible by cherry extinctions

**Setting.** Let $T$ be a rooted binary phylogenetic $X$-tree, $|X|=n$, with strictly positive edge lengths $\lambda_e$. The *Fair Proportion index* of a leaf $x$ is

$$FP_T(x)=\sum_{e\in P(T;\rho,x)}\frac{\lambda_e}{D_e},$$

where $P(T;\rho,x)$ is the root-to-$x$ path and $D_e$ the number of leaves below $e$; so $\sum_xFP_T(x)=\sum_e\lambda_e$, the phylogenetic diversity of $X$. A *cherry* is a pair of leaves with a common parent; $c_T$ is the number of cherries. For $X'\subset X$, $\widetilde T=T_{X\setminus X'}$ is the induced subtree (merging edge lengths). The ranking $\pi_T$ of $X$ by $FP_T$ is *strict* if $FP_T$ is injective, and *reversible* with respect to $X'$ if the ranking of $\widetilde X=X\setminus X'$ by $FP_{\widetilde T}$ is exactly the opposite of its ranking by $FP_T$.

**Theorem.**
1. (Necessity) If $|X|\ge3$ and $\pi_T$ is strict and reversible with respect to $X'$, then $X'$ contains at least one leaf of every cherry of $T$.
2. (Sufficiency) Let $n\ge2$ and let $\widetilde T$ be obtained from $T$ by deleting one leaf from each cherry. Then there are strictly positive edge lengths for $T$ for which $\pi_T$ is strict and reversible with respect to $\widetilde T$; moreover the leaf with highest $FP_T$ survives in $\widetilde T$ (where it becomes lowest), and the leaf with lowest $FP_T$ is deleted. Thus $FP_T(x_1)>\dots>FP_T(x_n)$ while the $n-c_T$ survivors satisfy $FP_{\widetilde T}(x_1)<FP_{\widetilde T}(\tilde x_2)<\dots<FP_{\widetilde T}(\tilde x_{n-c_T})$.
3. (Caterpillars) For every $n\ge2$ the caterpillar tree has edge lengths for which deleting only the species with the lowest FP index reverses the whole ranking.
4. (Realizability) For every rooted binary tree and every vector $\theta\in\mathbb R_+^n$ there are strictly positive edge lengths with $FP_T(x_i)=\theta_i$ for all $i$.

## Expansion

If both leaves $x_i,x_j$ of a cherry survive, deletions elsewhere change their FP values by the same amount (they share every edge except their own pendant edges, which keep length and descendant count), so their relative order cannot flip, contradicting reversibility. For sufficiency, induct on $n$ with $T=(T_a,T_b)$: deleting leaves raises the FP values of survivors (shared edges are split among fewer descendants), and two rescaling moves preserve strict reversible rankings, namely multiplying all edge lengths by $k>0$ (scales every FP value by $k$) and adding $d>0$ to every pendant edge (shifts every FP value by $d$). These let one interleave the reversed rankings of $T_a$ and $T_b$ consistently and choose the two root edges. The caterpillar has a single cherry, so item 3 is item 2 there.

## Sources

- M. Fischer, A. Francis, K. Wicke, "Phylogenetic diversity rankings in the face of extinctions: the robustness of the Fair Proportion index", arXiv:2107.00748 (2021), <https://doi.org/10.48550/arXiv.2107.00748>. Section 3.1 (Theorems 1 and 2, Corollary 1) and the Appendix (Lemmas 1–5 and 7, Corollary 2).

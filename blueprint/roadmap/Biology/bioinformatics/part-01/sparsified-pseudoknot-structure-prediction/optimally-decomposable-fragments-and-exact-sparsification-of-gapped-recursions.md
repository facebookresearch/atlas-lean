# Optimally decomposable fragments and exact sparsification of gapped recursions

Dynamic programmes for pseudoknotted structures (Rivas–Eddy class) tabulate optimal scores $W(F)$ of **ungapped fragments** $F = (i,j) = \{i,\dots,j\}$ and **1-gap fragments** $F = (i,j;k,l) = \{i,\dots,j\} \cup \{k,\dots,l\}$. Each recursion case has a **split type** $T$ (labels such as $12$, $1212$, $12G2$, $12G21$, $12G12$, $121G2$, describing how $F$ is cut into $F_1, F_2$) and maximizes $W(F_1) + W(F_2)$ over splits of that type; in base-pair maximization

$$W(i,j) = \max\Big\{ W(i,j-1),\ \mathrm{bp}(i,j) + W(i+1,j-1),\ \max_{j'} W(i,j'-1) + W(j',j),\ \max_{j',k',l'} W(i,j'-1;k'+1,l'-1) + W(j',k';l',j) \Big\},$$

with analogous cases for $W(i,j;k,l)$, giving $O(n^6)$ time and $O(n^4)$ space.

**Definition.** $F$ is **optimally decomposable by type $T$** ($T$-OD) if some split $(F_1,F_2)$ of type $T$ satisfies $W(F_1) + W(F_2) \ge W(F)$; it is $\mathcal{T}$-OD for a set $\mathcal{T}$ of types if it is $T$-OD for some $T \in \mathcal{T}$.

For each recursion case $T$ fix a set $\mathcal{T}^{RE}_T$ (for instance $\mathcal{T}^{RE}_{12} = \{12\}$, $\mathcal{T}^{RE}_{12G21} = \{12G2, 1G12, 12G21\}$) such that whenever the second fragment $F_2$ of a split is $\mathcal{T}^{RE}_T$-OD, an equally good split of the same type $T$ exists with second fragment strictly inside $F_2$. The **sparsified recursion** $W'$ is obtained by maximizing in each case $T$ only over second fragments that are not $\mathcal{T}^{RE}_T$-OD (the candidates).

**Theorem.** $W(1, |S|) = W'(1, |S|)$; in fact $W = W'$ on every fragment.

The resulting time is $O\big(n^2 (Z_{12} + Z_{1212}) + n^4 \sum_T Z_T\big)$ over the gapped cases, with space $O(n^3 + Z)$, where $Z_T$ is the maximal candidate-list length for case $T$ and $Z$ the total list size; the same construction applies to the energy-minimizing Rivas–Eddy and Dirks–Pierce algorithms.

## Depends on

- [Candidate sparsification of canonical pseudoknot recursions](candidate-sparsification-of-canonical-pseudoknot-recursions.md)
- [The Nussinov recursion](../../nussinov-algorithm-for-rna-secondary-structure/nussinov.md)

## Expansion

Clearly $W' \le W$. For the reverse, induct on fragment size: if $(j',j)$ is $12$-OD via $W(j',j) = W(j', j''-1) + W(j'',j)$, then $W(i, j''-1) + W(j'',j) \ge W(i,j'-1) + W(j',j''-1) + W(j'',j) = W(i,j'-1) + W(j',j)$ by the triangle inequality, so the split at $j''$ with a smaller second fragment is at least as good; repeating terminates at a candidate. Each gapped case has an analogous inequality. Testing $T$-OD costs nothing extra, since after evaluating case $T$ for $W(F)$ one compares its maximum with $W(F)$.

## Sources

- M. Möhl, R. Salari, S. Will, R. Backofen and S. C. Sahinalp, "Sparsification of RNA structure prediction including pseudoknots", Algorithms for Molecular Biology 5 (2010), 39, R&E recursions, Definition 2, the sets of split types and Theorem 1, <https://doi.org/10.1186/1748-7188-5-39>, PMCID: PMC3161351.

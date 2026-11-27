# Weighted cograph editing of orthology relation graphs

Let $\Gamma$ be a gene family with species map $s : \Gamma \to \Sigma$ and $S$ a rooted binary species tree on $\Sigma$. A **DS-tree** is a rooted binary tree $G$ with leaf set $\Gamma$ whose internal nodes are labelled $\mathrm{Spec}$ or $\mathrm{Dup}$; genes $x, y$ are orthologous in $G$ if $\mathrm{lca}_G(x, y)$ is a speciation and paralogous otherwise. With the LCA mapping $s_G(g) = \mathrm{lca}_S\{s(g') : g' \in L(G_g)\}$, a speciation node with children $v_1, v_2$ is **$S$-consistent** if neither of $s_G(v_1), s_G(v_2)$ is an ancestor of the other, and $G$ is $S$-consistent if all its speciation nodes are.

A **relation graph** $R$ on $\Gamma$ has edges for orthologies and non-edges for paralogies (genes of the same species are never adjacent). $R$ is **satisfiable** if $R = R(G)$ for some DS-tree $G$, which holds if and only if $R$ is $P_4$-free (a cograph), and **$S$-consistent** if this $G$ can be chosen $S$-consistent. Given weights $w$ on vertex pairs ($w = \infty$ on same-species pairs), an **edge editing** inserts $E^+ \subseteq \bar E_R$ and removes $E^- \subseteq E_R$.

**Problems.** MinWES: find a minimum-weight editing $w(E^+) + w(E^-)$ making $R$ satisfiable. MinWEC: the same, making $R$ $S$-consistent.

**Theorem 1 (inapproximability).** Assuming the unique games conjecture, minimum weighted cograph deletion, and hence MinWES and MinWEC, cannot be approximated within any constant factor.

**Lemma (superadditivity).** If $\sigma_Z$ denotes the optimal MinWES cost on $R[Z]$, then $\sigma_R \ge \sigma_X + \sigma_Y$ for every partition $\{X, Y\}$ of the vertices.

**Theorems 2–3 ($n$-approximation).** Recursively applying a minimum-weight cut of $R$ or of its complement $\bar R$ (for MinWEC: the unique cut of $\bar R$ that separates genes by the two root clades of $S$ restricted to the species present) and editing the cut pairs yields a correction of cost at most $n\,\sigma$, with $n = |\Gamma|$; the factor $n$ is tight up to an additive constant for this algorithm.

## Depends on

- [Is LCAReconciliation](../../../not-yet-classified/lcareconciliation/is-lcareconciliation.md)

## Expansion

Every cograph on two or more vertices is disconnected or has a disconnected complement, matching a root that is a duplication (no orthologies across the two sides) or a speciation (all pairs across are orthologous). The recursive algorithm forces this structure by cutting; by induction its cost is at most $|X|\sigma_X + |Y|\sigma_Y + w(C) \le (n-1)(\sigma_X + \sigma_Y) + \sigma_R \le n\sigma_R$, using that some cut of $R$ or $\bar R$ is no more expensive than an optimal editing and superadditivity. Hardness comes from a gap-preserving reduction from minimum multicut. In the consistent variant a speciation must separate genes exactly according to the species tree, which fixes the cut on the complement side.

## Sources

- R. Dondi, M. Lafond, N. El-Mabrouk, "Approximating the correction of weighted and unweighted orthology and paralogy relations", Algorithms for Molecular Biology 12 (2017) 4, Definitions 1–2, problem statements MinWES and MinWEC, Theorem 1 with Corollaries, Lemmas 4–5 and Theorems 2–3, <https://doi.org/10.1186/s13015-017-0096-x>, PMCID PMC5346272.

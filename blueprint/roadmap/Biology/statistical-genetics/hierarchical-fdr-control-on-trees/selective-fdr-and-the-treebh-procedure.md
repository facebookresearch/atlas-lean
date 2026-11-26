# Selective false discovery rate and the TreeBH procedure

Let hypotheses be arranged in a rooted tree with levels $0, \dots, L$, each hypothesis having one parent, so that if a null hypothesis is true all its descendants are true. Children of the same parent $H_i$ at level $\ell - 1$ form the family $\mathcal{F}_i^{\ell}$. Testing is hierarchical: a family is tested only if its parent was rejected (the root is tested at level $q^{(0)}$, or regarded as always rejected). For a rejected hypothesis $H_j$ let $\mathcal{S}_j$ be the set of rejected hypotheses in the family it indexes, and $A(i)$ the set of ancestors of $H_i$.

**Selective error rate.** For a target level $\ell$, assign to each hypothesis rejected at level $\ell$ the error $\mathcal{E}_i(\ell) = 1$ if $H_i$ is a true null and $0$ otherwise, and recursively to each rejected hypothesis $H_j$ at a coarser level the average error of its rejected children, $\mathcal{E}_j(\ell) = \sum_{r \in \mathcal{S}_j}\mathcal{E}_r(\ell)/|\mathcal{S}_j|$ (with $0/0 = 0$). The selective false discovery rate at level $\ell$ is

$$\mathrm{sFDR}_\ell = \mathbb{E}\{\mathcal{E}_0(\ell)\}.$$

Equivalently $\mathcal{E}_0(\ell) = \sum_{i \in \mathcal{S}^{\ell-1}} w_i^{\ell}\,\mathrm{FDP}(\mathcal{F}_i^{\ell})$, a weighted average of the false discovery proportions of the selected level-$\ell$ families with random weights $w_i^{\ell} = 1/\prod_{j \in A(i)}|\mathcal{S}_j|$ for $\ell > 1$ and $w_0^1 = 1$. If the root is always rejected, $\mathrm{sFDR}_1$ is the ordinary false discovery rate of the first level.

**TreeBH procedure.** Given targets $q^{(1)}, \dots, q^{(L)}$:

1. Apply the [Benjamini–Hochberg procedure](../../../Probability/hypothesis-testing/benjamini-hochberg-procedure/bh-rejections.md) at level $q^{(1)}$ to the family $\mathcal{F}_0^{1}$; stop if nothing is rejected.
2. For $\ell = 2, \dots, L$: for every family $\mathcal{F}_i^{\ell}$ whose parent $H_i$ was rejected, apply the Benjamini–Hochberg procedure with working level

$$q_i = \Bigg\{\prod_{j \in A(i)}\frac{|\mathcal{S}_j|}{|\mathcal{F}_j|}\Bigg\}\,q^{(\ell)},$$

where $\mathcal{F}_j$ is the family containing the children of $H_j$; stop when no rejections are made or $\ell = L$.

Parent $p$-values are typically obtained by Simes' rule from their children, $p_i = \min_j p_{(j)}\,k/j$ over the $k$ sorted $p$-values of the family.

## Depends on

- [Benjamini–Hochberg rejection set](../../../Probability/hypothesis-testing/benjamini-hochberg-procedure/bh-rejections.md)

## Expansion

The weight of a family's false discovery proportion is small when many rejections were made along the branch that selected it, and large when the branch was selected narrowly; the working levels $q_i$ of TreeBH mirror exactly these weights, extending the Benjamini–Bogomolov adjustment for two levels to arbitrarily many. Unlike the global false discovery rate at level $\ell$, $\mathrm{sFDR}_\ell$ cannot be kept small by many true discoveries in one rich family masking false discoveries scattered over many sparse families.

## Sources

- M. Bogomolov, C. B. Peterson, Y. Benjamini and C. Sabatti, "Hypotheses on a tree: new error rates and testing strategies", Biometrika 108 (2021), 575–590, <https://doi.org/10.1093/biomet/asaa086> (PMC9945647), sections 2–4.1, Equations (1)–(2).

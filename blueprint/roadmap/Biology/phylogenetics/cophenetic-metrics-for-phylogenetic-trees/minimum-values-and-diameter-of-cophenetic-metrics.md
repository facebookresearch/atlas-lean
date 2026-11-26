# Minimum values and diameter of cophenetic metrics

For phylogenetic trees $T_1, T_2$ on $S = \{1,\dots,n\}$ with cophenetic vectors $\varphi(T_1), \varphi(T_2) \in \mathbb{R}^{n(n+1)/2}$, and $p \in \{0\} \cup [1, \infty)$, the **cophenetic metric** is

$$d_{\varphi,p}(T_1,T_2) = \big\|\varphi(T_1) - \varphi(T_2)\big\|_p,$$

where $\|\cdot\|_0$ counts nonzero entries; set $D_0 = d_{\varphi,0}$ and $D_p = d_{\varphi,p}^{\,p}$ for $p \ge 1$, so $D_p = \sum |\varphi_{T_1}(i,j) - \varphi_{T_2}(i,j)|^p$. Write $UT_n$ for unweighted trees (nested taxa allowed), $T_n$ for unweighted trees without nested taxa and $BT_n$ for the binary ones.

1. On $UT_n$ ($n \ge 2$) the minimum nonzero value of $D_p$ is $1$, attained exactly when one tree is obtained from the other by contracting a pendant arc.
2. On $T_n$ ($n \ge 3$) the minimum nonzero value of $D_p$ is $3$, attained exactly when one tree is obtained from the other by contracting an arc ending in the parent of a cherry, or by pruning a leaf that is a sibling of the root of a cherry and regrafting it as a sibling of the cherry's leaves.
3. On $BT_n$ ($n \ge 3$) the minimum nonzero value of $D_p$ is $4$, attained exactly when one tree is obtained from the other by reorganizing a triplet or reorganizing a completely branched quartet.
4. The diameter of $d_{\varphi,p}$ on $UT_n$, $T_n$ and $BT_n$ is of order $\Theta(n^2)$ for $p = 0$ and $\Theta(n^{(p+2)/p})$ for $p \ge 1$; in particular $\Theta(n^3)$ for $p = 1$ and $\Theta(n^2)$ for $p = 2$.

## Depends on

- [Cophenetic vectors single out rooted phylogenetic trees](cophenetic-vectors-single-out-rooted-phylogenetic-trees.md)

## Expansion

Because unweighted cophenetic values are integers, $D_p \ge D_0$ for every $p \ge 1$; hence whenever the pairs minimizing $D_0$ change every differing entry by exactly one, the minimum of $D_p$ equals that of $D_0$ and is attained at the same pairs. Each listed local move shifts the depth of one LCA (and the depths below it) by one unit, changing exactly 1, 3 or 4 entries. Unlike the Robinson–Foulds distance, cophenetic metrics take many distinct values and correlate only moderately with split- and path-length-based distances in exhaustive comparisons for $n \le 6$.

## Sources

- G. Cardona, A. Mir, F. Rosselló, L. Rotger and D. Sánchez, "Cophenetic metrics for phylogenetic trees, after Sokal and Rohlf", BMC Bioinformatics 14 (2013), 3, Lemma 1 and Propositions 1–4, <https://doi.org/10.1186/1471-2105-14-3>, PMCID: PMC3716993.

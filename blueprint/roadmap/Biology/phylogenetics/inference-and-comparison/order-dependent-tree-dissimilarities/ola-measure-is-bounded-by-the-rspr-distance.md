# OLA measure is bounded by the rSPR distance

**OLA vector.** Let $T$ be a rooted binary phylogenetic $X$-tree with $|X| = n$ and $\sigma$ an ordering of $X$. Label each leaf $x$ by $\sigma(x)$. Grow $T$ by starting from $T|\{\rho, \sigma^{-1}(1), \sigma^{-1}(2)\}$, whose internal vertex gets label $-2$, and for $i = 3, \dots, n$ adjoin $\sigma^{-1}(i)$ so that the current tree is $T|\{\rho, \sigma^{-1}(1), \dots, \sigma^{-1}(i)\}$, labeling the new attachment vertex $-i$ and recording the label $f(s_i)$ of the sibling $s_i$ of $\sigma^{-1}(i)$ at that moment. The **OLA vector** is $[0, 1, f(s_3), \dots, f(s_n)]$, and $d^\sigma_{\mathrm{OLA}}(T, T')$ is the Hamming distance between the OLA vectors of $T$ and $T'$ under $\sigma$ (a metric for fixed $\sigma$). The **OLA measure** is $d^*_{\mathrm{OLA}}(T, T') = \min_\sigma d^\sigma_{\mathrm{OLA}}(T, T')$.

**rSPR distance.** An rSPR move deletes a non-root edge $(u, v)$, suppresses $u$ and reattaches the subtree rooted at $v$ by subdividing an edge of the component containing $\rho$. $d_{\mathrm{rSPR}}(T, T')$ is the minimum number of moves turning $T$ into $T'$; it equals $m(T, T')$, the minimum number of components minus one of an agreement forest for $T$ and $T'$.

**Statement.** For all rooted binary phylogenetic $X$-trees $T, T'$ there is an ordering $\sigma$ of $X$ with

$$d^\sigma_{\mathrm{OLA}}(T, T') \le 28\, d_{\mathrm{rSPR}}(T, T'),$$

and hence $d^*_{\mathrm{OLA}}(T, T') \le 28\, d_{\mathrm{rSPR}}(T, T')$. Whether the constant 28 can be lowered is open.

## Expansion

Apply the subtree reduction (replace a maximal common pendant subtree by one leaf) and the chain reduction (shorten a maximal common chain to three leaves) until neither applies. Choosing $\sigma$ so that reduced leaves and the three chain leaves receive consecutive ranks, in increasing order along each chain, makes each reduction leave the OLA Hamming distance unchanged. The fully reduced pair has at most $28\, d_{\mathrm{rSPR}}(T, T')$ leaves (the linear kernel for the rSPR distance), and the Hamming distance of two OLA vectors is at most their length, which gives the bound.

## Sources

- S. Linz, K. St. John, C. Semple and K. Wicke, "Order-dependent dissimilarity measures on phylogenetic trees", *Journal of Mathematical Biology* 92(4) (2026), 53, Theorem 1, Theorem 3, Lemmas 2 and 3, Problem 2, <https://doi.org/10.1007/s00285-026-02373-7> (preprint arXiv:2507.11254).

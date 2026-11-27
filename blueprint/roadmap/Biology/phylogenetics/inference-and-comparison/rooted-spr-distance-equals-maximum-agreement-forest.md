# Fixed-parameter tractability of the rooted SPR distance

For rooted binary phylogenetic $X$-trees $T, T'$, the rooted subtree prune and regraft distance equals the maximum agreement forest number, $d_{\mathrm{rSPR}}(T, T') = m(T, T')$ ([Bordewich and Semple 2005, Theorem 2.1](../../not-yet-classified/rooted-spragreement-forest/rspr-dist-eq-rooted-maf-number.md)), and its decision problem is [NP-complete](../../not-yet-classified/rooted-spragreement-forest/rspr-distance-np-complete.md) (Theorem 1.1 and Corollary 2.2). Bordewich and Semple (2005, Theorem 3.4) prove that the decision problem parameterized by the distance is fixed-parameter tractable: repeated subtree and chain reductions (Rules 1 and 2*) preserve the distance and give trees with at most $28d$ leaves at distance $d \ge 1$ (Lemma 3.3); distance $0$ means $T = T'$, where the reduced trees still have a leaf, so that case is decided directly by comparing the trees and is excluded from the bound. Hence the question $d_{\mathrm{rSPR}}(T, T') \le k$ is decided in time $O((56k)^{2k}p(|X|))$ for a polynomial $p$.

## Depends on

- [rSPR distance equals the maximum agreement forest number](../../not-yet-classified/rooted-spragreement-forest/rspr-dist-eq-rooted-maf-number.md)

## Expansion

1. The reduction rules 1 and 2* and the invariance of $d_{\mathrm{rSPR}}$ under them.
2. The bound $28d$ on the reduced leaf set for $d \ge 1$ (Lemma 3.3), and the separate equality test for $d = 0$.
3. The resulting fixed-parameter algorithm and its running time.

## Sources

- M. Bordewich and C. Semple, On the computational complexity of the rooted subtree prune and regraft distance, Ann. Comb. 8 (2005), 409–423, Theorems 1.1, 2.1 and 3.4 and Corollary 2.2. <https://doi.org/10.1007/s00026-004-0229-z>

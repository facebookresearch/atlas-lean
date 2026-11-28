# Fixed-parameter tractability of the rooted SPR distance

For rooted binary phylogenetic $X$-trees $T, T'$, the rooted subtree prune and regraft distance equals the maximum agreement forest number, $d_{\mathrm{rSPR}}(T, T') = m(T, T')$ ([Bordewich and Semple 2005, Theorem 2.1](../../../not-yet-classified/rooted-spragreement-forest/rspr-dist-eq-rooted-maf-number.md)), and its decision problem is [NP-complete](../../../not-yet-classified/rooted-spragreement-forest/rspr-distance-np-complete.md) (Theorem 1.1 and Corollary 2.2). Bordewich and Semple (2005, Theorem 3.4) prove that the decision problem parameterized by the distance is fixed-parameter tractable, with an explicit running time: the question $d_{\mathrm{rSPR}}(T, T') \le k$ is decided in time $O((56k)^{2k}p(|X|))$ for a polynomial $p$. The proof first applies subtree and chain reductions; that these reductions preserve the agreement forest number, and that fully reduced pairs at distance $d \ge 1$ have linearly many leaves in $d$, are the two-tree case of the [linear kernel for maximum agreement forest on multiple trees](linear-kernel-for-maximum-agreement-forest-on-multiple-trees.md) and are not restated here. Distance $0$ means $T = T'$, which is decided directly by comparing the trees.

## Depends on

- [rSPR distance equals the maximum agreement forest number](../../../not-yet-classified/rooted-spragreement-forest/rspr-dist-eq-rooted-maf-number.md)

## Proof depends on

- [Linear kernel for maximum agreement forest on multiple trees](linear-kernel-for-maximum-agreement-forest-on-multiple-trees.md)

## Expansion

1. The reduced instance: the bound of at most $28k$ leaves after reduction (Lemma 3.3 of the source) for distance at most $k \ge 1$, and the separate equality test for distance $0$.
2. The search over the reduced trees and the resulting running time $O((56k)^{2k}p(|X|))$.

## Sources

- M. Bordewich and C. Semple, On the computational complexity of the rooted subtree prune and regraft distance, Ann. Comb. 8 (2005), 409–423, Theorems 1.1, 2.1 and 3.4 and Corollary 2.2. <https://doi.org/10.1007/s00026-004-0229-z>

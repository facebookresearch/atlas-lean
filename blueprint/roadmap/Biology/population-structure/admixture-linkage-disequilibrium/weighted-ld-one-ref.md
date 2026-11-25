# Weighted LD amplitude with one diverged reference

Let $M$ be a [drift model](../patterson-s-f-statistics/drift-model.md) on an s-finite measure $\mu$ with lineage weights $w$, and let $A, B, C, R', R''$ be populations and $u_A, u_B, u_R \in \mathbb{R}^E$ with $w(A, \cdot) = w(R'', \cdot) + u_A$, $w(B, \cdot) = w(R'', \cdot) + u_B$, $w(R', \cdot) = w(R'', \cdot) + u_R$, where $u_A u_B$, $u_A u_R$ and $u_B u_R$ vanish at every edge, and $w(C, \cdot) = \alpha\, w(A, \cdot) + (1 - \alpha)\, w(B, \cdot)$ for a real $\alpha$. Then for every real $r$ and natural number $n$, the [weighted LD integral](weighted-ld.md) with references $R'$ and $C$ is

$$W = 2 \alpha (1 - \alpha) (1 - r)^n \bigl(\alpha\, f_2(A, R'') - (1 - \alpha)\, f_2(B, R'')\bigr)^2$$

the discrete-generation analogue of Loh et al. (2013), Eq. 8, whose formula has $e^{-nd}$ in place of $(1 - r)^n$ ([exact and continuous decay factors](exp-neg-mul-le-pow-one-sub-haldane.md)).

## Sources

- P.-R. Loh, M. Lipson, N. Patterson, P. Moorjani, J. K. Pickrell, D. Reich, B. Berger, *Inferring admixture histories of human populations using linkage disequilibrium*, Genetics 193 (2013), 1233–1254, Eq. 8.

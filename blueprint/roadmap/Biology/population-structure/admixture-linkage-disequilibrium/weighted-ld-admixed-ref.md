# Weighted LD amplitude with the admixed population as reference

Let $M$ be a [drift model](../patterson-s-f-statistics/drift-model.md) on an s-finite measure $\mu$ with lineage weights $w$, and let $A, B, C$ be populations with $w(C, \cdot) = \alpha\, w(A, \cdot) + (1 - \alpha)\, w(B, \cdot)$ for a real $\alpha$ (no drift in $C$ after the pulse). Then for every real $r$ and natural number $n$, the [weighted LD integral](weighted-ld.md) with references $A$ and $C$ is

$$W = 2 \alpha (1 - \alpha)^3 (1 - r)^n\, f_2(A, B)^2$$

the discrete-generation analogue of Loh et al. (2013), Eq. 7, whose formula has $e^{-nd}$ in place of $(1 - r)^n$ ([exact and continuous decay factors](exp-neg-mul-le-pow-one-sub-haldane.md)).

## Sources

- P.-R. Loh, M. Lipson, N. Patterson, P. Moorjani, J. K. Pickrell, D. Reich, B. Berger, *Inferring admixture histories of human populations using linkage disequilibrium*, Genetics 193 (2013), 1233–1254, Eq. 7.

# Dyadic zero count and local counts for primitive Dirichlet L-functions

Fix a primitive complex character $\chi$ of modulus $q>1$. Count zeros of $L(s,\chi)$ with multiplicity in the open critical strip and ordinate in $(a,b]$. For this fixed modulus and character the dyadic main term is

$$
N_\chi(T,2T)=\frac{T}{2\pi}\left(\log\frac{qT}{2\pi}+2\log2-1\right)+O_{q,\chi}(\log T)\quad(T\to+\infty).
$$

For some $A\ge1$ depending on the fixed modulus and character, $N_\chi(t,t+1)\le A\log(|t|+3)$ for every real $t$. Both estimates count analytic orders, not distinct points; neither assumes the ordinate avoids zeros in the final statement.

## Depends on

- [Zeros in a window](../../riemann-zeta/zeros-of-the-riemann-zeta-function/window-zeros.md)
- [The open critical strip](../../riemann-zeta/zeros-of-the-riemann-zeta-function/open-critical-strip.md)
- [Count with multiplicity](../../riemann-zeta/zeros-of-the-riemann-zeta-function/count-with-multiplicity.md)

## Proof depends on

- [Argument principle for a piecewise smooth Jordan contour](../../../../Analysis/complex-analysis/cauchy-theory/argument-principle/argument-principle-on-a-piecewise-smooth-jordan-contour.md)

## Expansion

Use the conductor and parity in the gamma factor and the functional equation with the conjugate character. Establish the folded count on good ordinates, a local bound on both signs of the ordinate, and the passage to arbitrary endpoints. A bound on a primitive fixed character suffices here; no uniformity across moduli is being used in the proportion claims.

## Sources

- Anthropic, [formalized argument](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/ThmE/RvMChi.lean#L24-L43).
- Anthropic, [formalized argument](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/ThmE/MainTermChi.lean).
- Anthropic, [formalized argument](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/ThmE/LocalCountChi.lean).

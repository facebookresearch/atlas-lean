# Interlaced variational objectives for spherical codes

Let $a_0>b_0>a_1>\cdots>b_{r-1}>a_r\ge0$ be real interlacing arrays, with just $a_0\ge0$ at level $r=0$. Define $q(u)=u(1+u)$, $h_S(u)=(1+u)\log_2(1+u)-u\log_2 u$ (zero log product at zero), and

$$w_\ell=\frac{\prod_{j<r}(q(a_\ell)-q(b_j))}{\prod_{j\ne\ell}(q(a_\ell)-q(a_j))},\qquad
\Gamma(a,b)=\sum_{\ell=0}^{r} w_\ell\frac{\sqrt{q(a_\ell)}}{1+2a_\ell},\qquad
\Phi(a,b)=\sum_{\ell=0}^{r}h_S(a_\ell)-\sum_{j=0}^{r-1}h_S(b_j).$$

The level rate $L_r(s)$ is the infimum of $\Phi$ over level-$r$ arrays with $s<2\Gamma$. The closed hierarchy rate $L_{\rm cl}(s)$ takes the infimum over all levels, with weak constraint $s\le2\Gamma$ but still strict interlacing. Empty products are one.

## Implementation notes

Formalize the finite interlacing indices, distinct transformed coordinates and nonzero denominators. Establish bounds and nonemptiness for all level infima used on the intended range, and keep the strict and weak spectral constraints separate.

## Sources

- [Pinned hierarchy and closed feasible sets](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/B_SphericalCodes.lean#L190-L250)

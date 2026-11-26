# Ample rank-two bundles without Griffiths-positive metrics

On $Q=\mathbb P^1_{\mathbb C}\times\mathbb P^1_{\mathbb C}$, put $p_m([a:b],[c:d])=([a^m:b^m],[c^m:d^m])$ for $m\ge1$. There exist a rank-two algebraic bundle $G$ and bundles $E_m$ with $E_m=p_m^*G\otimes\mathcal O(1,1)$ for every integer $m>0$. Every such $E_m$ is ample, and for some $m_0>0$ no $E_m$ with $m\ge m_0$ admits a smooth strictly Griffiths-positive Hermitian metric. Ampleness here means some positive power of the tautological line on the projectivization of the dual is cut out by a finite system of sections giving a closed projective embedding: the homogeneous evaluations have no base point, separate projective points, have Zariski-closed projective image, and admit regular local inverses.

In a dual frame with positive Hermitian matrix $H$, the strict condition is positive definiteness of $H_{u\bar u}-(H_u)^*H^{-1}H_u$ at each chart point for every nonzero complex direction $u$, with $H_u=(D_uH-iD_{iu}H)/2$ and $H_{u\bar u}=(D_u^2H+D_{iu}^2H)/4$. The chart model trivializes over finitely many principal opens in the standard four affine charts, and the twisted cocycle is the pullback cocycle multiplied by the coordinate transition for $\mathcal O(1,1)$. This is not a claim of very ampleness for every admissible even exponent.

## Depends on

- [Complex atlas](../../AlgebraicGeometry/not-yet-classified/hyperkahler-complex-structures/complex-atlas.md)
- Principal-open bundle cocycles, projectivization with dual transition matrices, and curvature invariant under change of frame.

## Proof depends on

- Algebraic embedding from the chosen symmetric-power sections; obstruction to positivity for sufficiently large pullbacks.

## Expansion

Build the comparison between the principal-chart cocycle model and native bundles, including the dual curvature sign. Separately verify the section separation, local inverse, and curvature obstruction before combining them for the same family.

## Sources

- OpenAI Math, [`main_theorem`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/QuadricBundles.lean#L174-L176) (statement and local definitions).

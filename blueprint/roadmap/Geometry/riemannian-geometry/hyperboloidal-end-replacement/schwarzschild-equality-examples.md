# Schwarzschild equality examples at every positive mass

Fix $m>0$. On the exterior $[0,\infty)\times S^2$, send the height-direction pair $(h,n)$ to $x=(2m+h)n$. At $r=|x|$ let $V(r)=-1+(r+1)\chi(r-2m-1)$ for the smooth transition $\chi$ from $0$ to $1$, and let $B^2(r)=1-2m/r+V(r)^2$ with $B(r)=\sqrt{B^2(r)}$. Write $dr_x(a)=\langle x/r,a\rangle$ and $\delta$ for the spatial Euclidean form. Take the metric and tensor defined by the pullbacks of

$$g_{\rm cart}=\delta+(B^{-2}-1)\,dr^2,\qquad K_{\rm cart}=(V/r)\delta+(V'/B^2-V/r)\,dr^2.$$

There exist a smooth metric with this pointwise inner product, a CKS end description for this pair, and an atlas of smooth open-neighborhood full-rank coefficient realizations of both fields. Together these satisfy the following: orientability, completeness, a smooth symmetric tensor, the physical dominant energy condition in the coefficient model, strictly future-timelike charge, compact nonempty connected boundary, and positive minimum enclosing area. For marginality, the boundary has its own coefficient realizations and a unit normal orthogonal to the boundary's tangent image, smooth when expressed in those coefficients and with positive first half-space component (inward). The expansion $H+\operatorname{tr}_{\partial N}K$ for that normal vanishes. Separately, the chosen interior coefficient atlas excludes any compact nonempty Hausdorff second-countable smooth surface embedded in the interior with injective derivative and coefficient-smooth unit normal: the excluded surface must be the frontier of a regular closed region with nonempty interior contained inside some finite end radius, and on each connected component one of $H\pm\operatorname{tr}_{T}K$ must vanish identically. The choice of sign can vary by component.

The equality data include the regularity of the actual advanced-time graph. On spacetime $(v,x)$ with $r=|x|$, the bilinear form is

$$\mathbf g=-(1-2m/r)\,dv^2+dv\otimes dr+dr\otimes dv+\delta-dr^2.$$

Use the source's totalized radial formulas at the center. The form is symmetric everywhere and smooth and nondegenerate off $x=0$. Set $A(r)=[B(r)(B(r)-V(r))]^{-1}$, $v(r)=\int_{2m}^r A(s)\,ds$ and $\Phi(x)=(v(|x|),x)$. The graph map is injective, smooth on $r>m$, and for every $a$ at such $x$ its derivative is $(A(r)dr_x(a),a)$. At $r=2m$ the advanced time is zero and $A(2m)=1/2$.

For every $r\ge2m$, along the graph the specified normal $((B-V)^{-1},Vx/r)$ has squared length $-1$, is orthogonal to every graph tangent and has positive advanced-time component. On that whole closed exterior the form on pairs of graph tangents is $g_{\rm cart}$, and the form pairing the covariant derivative of this normal along one graph tangent with the other tangent is $K_{\rm cart}$, with the sign as written. For these same data, $m_{\rm Bondi}=m$, $A_{\min}=16\pi m^2$, and $m_{\rm Bondi}=\sqrt{A_{\min}/(16\pi)}$. This is existence of equality data, not uniqueness of equality cases or the general inequality.

## Depends on

- Advanced Schwarzschild form, exact graph and second form with their signs, and the chosen exterior manifold.
- CKS mass aspect, full-rank coefficient realizations, boundary normal and null expansions, and outer-domain area infimum, with the source conventions in [area-controlled end replacement](area-controlled-end-replacement.md).

## Proof depends on

- The horizon-smooth graph and normal calculations with the indicated domains, the CKS asymptotics, marginality, exclusion of additional separating horizons, and the sharp lower area bound for all cuts.

## Expansion

Verify the exact ambient form, graph derivative, timelike normal and induced forms before the asymptotic charge calculation. Separate horizon and global area calculations without assuming an unproved general Bondi–Penrose inequality.

## Sources

- OpenAI Math, [`schwarzschild_equality_examples`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CKSBondiPenrose.lean#L3568-L3593).
- OpenAI Math, [advanced metric, graph and horizon conditions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CKSBondiPenrose.lean#L3150-L3219) and [initial-data hypotheses](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CKSBondiPenrose.lean#L3511-L3552).

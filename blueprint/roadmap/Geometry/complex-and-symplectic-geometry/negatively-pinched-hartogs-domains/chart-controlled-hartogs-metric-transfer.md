# Complete negatively pinched metrics from controlled Hartogs potentials

Let $B=\{z\in\mathbb C^2:\|z\|<1\}$. For $0\le r<1$ and unitary $U$, use the centered chart

$$q_{r,U}(\zeta)=U\left(\frac{r+\zeta_1}{1+r\zeta_1},\frac{\sqrt{1-r^2}\,\zeta_2}{1+r\zeta_1}\right).$$

    Say a smooth real $\phi$ has chart bounds $(c,C)$ when the complex Hessian of $\phi\circ q_{r,U}$ at $0$ is between $cI$ and $CI$ for all the charts. Its jet bound $C$ bounds, for every entry and every choice of coordinate directions, the sum of the moduli of a holomorphic first derivative, an antiholomorphic first derivative, and the corresponding mixed second derivative of that Hessian, all at $0$.

For every real pair $0<c\le C$ there is $\lambda_0>0$ such that for every smooth $\phi$ on $B$ with chart bounds $(c,C)$ and jet bound $C$, and every $\lambda\ge\lambda_0$, the Hartogs domain $M_\phi=\{(z,w):z\in B,\ e^{\phi(z)}|w|^2<1\}$ is contractible, and the complex Hessian of

$$-\lambda\log(1-\|z\|^2)-\log(1-e^{\phi(z)}|w|^2)$$

is a geodesically complete Kähler metric on $M_\phi$. There are $0<A\le B'$ such that its real sectional curvature belongs to $[-B',-A]$ on every real two-plane. Geodesic completeness means a smooth solution on all real times of the Christoffel geodesic equation for every base point and tangent initial value.

## Depends on

- [Complex Hessian](../../../Analysis/complex-analysis/several-complex-variables/complex-hessian/complex-hessian.md)
- [Sectional curvature](../../riemannian-geometry/curvature-of-riemannian-manifolds/sectional-curvature.md)
- Hartogs-domain metric from a Hessian, Hermitian/real curvature comparison and completeness.

## Proof depends on

- Uniform curvature estimates in centered charts and completeness near both boundary components; contractibility.

## Expansion

Identify the complex curvature tensor and real sectional normalization. Prove a choice of threshold depending only on the two chart bounds before specializing the potential.

## Sources

- OpenAI Math, [`metric_transfer`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PinchedKahler.lean#L152-L154) (statement and local definitions).

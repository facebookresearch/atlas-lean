# A controlled potential with no bounded-growth holomorphic minorant

Let $B=\{z\in\mathbb C^2:\|z\|<1\}$. For $0\le r<1$ and unitary $U$, use the centered chart

$$q_{r,U}(\zeta)=U\left(\frac{r+\zeta_1}{1+r\zeta_1},\frac{\sqrt{1-r^2}\,\zeta_2}{1+r\zeta_1}\right).$$

    Say a smooth real $\phi$ has chart bounds $(c,C)$ when the complex Hessian of $\phi\circ q_{r,U}$ at $0$ is between $cI$ and $CI$ for all the charts. Its jet bound $C$ bounds, for every entry and every choice of coordinate directions, the sum of the moduli of a holomorphic first derivative, an antiholomorphic first derivative, and the corresponding mixed second derivative of that Hessian, all at $0$.

There are $\phi$ smooth on $B$ and real $C$ with chart bounds $(1,C)$ and jet bound $C$ such that there do not exist a holomorphic $H:B\to\mathbb C$ and a constant $D$ with $\operatorname{Re}H(z)\le D+4\log(1/(1-\|z\|))+\phi(z)$ for every $z\in B$.

## Depends on

- [Complex Hessian](../../../Analysis/complex-analysis/several-complex-variables/complex-hessian/complex-hessian.md)
- Complex Hessians and derivative jets in the explicit automorphism charts of the Euclidean complex ball.

## Proof depends on

- Plurisubharmonic potential construction with uniform lower Hessian bound and a simultaneous holomorphic minorant obstruction.

## Expansion

Track the exact chart normalization, jet bound and logarithm coefficient, and separate the analytic obstruction from smoothness and derivative bounds.

## Sources

- OpenAI Math, [`controlled_potential`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PinchedKahler.lean#L149-L151) (statement and local definitions).

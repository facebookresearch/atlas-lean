# Every fixed-traction solution equals the constructed displacement

Let $k \ne 0$ and let $L$ and $P$ be real numbers and $f \colon \mathbb{R} \to \mathbb{R}$. If $u$
solves the [fixed-traction problem](is-fixed-traction-solution.md) on $[0, L]$ with rigidity $k$,
load $f$ and end force $P$, then for every $x \in [0, L]$

$$u(x) = \int_0^x \frac{1}{k}\left(P + \int_y^L f(z)\, dz\right) dy,$$

the [fixed-traction displacement](fixed-traction-displacement.md). No condition on $L$ or $f$ is
needed (for $L < 0$ the interval is empty). Outside $[0, L]$, $u$ is not determined.

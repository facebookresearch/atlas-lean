# Load path: the internal force is the end force plus the load beyond x

Let $k$, $L$ and $P$ be real numbers, $f \colon \mathbb{R} \to \mathbb{R}$, and let $u$ solve the
[fixed-traction problem](is-fixed-traction-solution.md) on $[0, L]$ with rigidity $k$, load $f$ and
end force $P$. Then for every $x \in [0, L]$

$$k\, u'(x) = P + \int_x^L f(y)\, dy,$$

with $u'$ the derivative within $[0, L]$: the internal axial force at $x$ (tension positive) is the
end force plus the distributed load carried between $x$ and $L$. No further condition on $k$, $L$ or
$f$ is needed: for $L > 0$ the equation makes $f = -k\, u''$ continuous on $[0, L]$, for $L = 0$ the
identity is the end condition, and for $L < 0$ the interval is empty.

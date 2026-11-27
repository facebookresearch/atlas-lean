# Classification of expansion waves by the velocity ratio

**Setting.** A population of density $n(t, x)$ with carrying capacity $N$ expands into empty habitat according to

$$\partial_t n = D\, \partial_x^2 n + r(n)\, n,$$

where the per-capita growth rate $r(n)$ satisfies $r(N) = 0$ and $r(0) > 0$. Let $v$ be the asymptotic speed of the monotone front invading $n = 0$, and define the *Fisher (linear spreading) velocity*

$$v_F = 2\sqrt{D\, r(0)}.$$

Always $v \ge v_F$. In the frame $\zeta = x - vt$ the density decays at the leading edge as $e^{-k\zeta}$ with

$$k = \frac{v}{2D}\left(1 + \sqrt{1 - v_F^2/v^2}\right).$$

**Classification.**

- *Pulled* waves: $v = v_F$; the dynamics is driven by the low-density leading edge.
- *Semipushed* waves: $1 < v/v_F < \tfrac{3}{2\sqrt 2} \approx 1.06$; both bulk and edge contribute.
- *Fully pushed* waves: $v/v_F \ge \tfrac{3}{2\sqrt 2}$, and also whenever $r(0) < 0$ (strong Allee effect), where $v_F$ is undefined.

The transition at $v/v_F = 3/(2\sqrt 2)$ is universal: it is where the integrals weighting fluctuations by the squared front profile, whose integrands scale as $e^{(2v/D - 3k)\zeta}$, stop converging at the leading edge, i.e. $v/D = 3k/2$.

**Example.** For cooperative growth $r(n) = r_0 (1 - n/N)(1 + B n/N)$, expansions are pulled for $B \le 2$ and pushed with $v > v_F$ for $B > 2$.

## Depends on

- [Traveling front of the Fisher–KPP equation](../../../../Analysis/ordinary-differential-equations/is-front.md)

## Expansion

The ratio $v/v_F$ measures how much growth in the bulk accelerates the front beyond the linearized edge prediction. Substituting $v/D = 3k/2$ into the formula for $k$ gives $\sqrt{1 - v_F^2/v^2} = 1/3$, i.e. $v = \tfrac{3}{2\sqrt2} v_F$. Because only the edge decay rate enters, the threshold does not depend on the functional form of $r(n)$.

## Sources

- G. Birzu, O. Hallatschek and K. S. Korolev, "Fluctuations uncover a distinct class of traveling waves", *Proceedings of the National Academy of Sciences USA* (2018), Eqs. 1–3, 6–7 and the surrounding text. <https://doi.org/10.1073/pnas.1715737115> (PMC5910819)

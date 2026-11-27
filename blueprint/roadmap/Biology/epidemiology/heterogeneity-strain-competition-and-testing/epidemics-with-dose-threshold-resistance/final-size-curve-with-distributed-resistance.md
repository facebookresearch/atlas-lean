# Final size curve of an epidemic with distributed dose resistance

**Setting.** In the [Kermack–McKendrick epidemic with dose-threshold resistance](kermack-mckendrick-epidemic-with-dose-threshold-resistance.md), take distributed resistance with continuous probability density $\sigma : \mathbb{R}_+ \to \mathbb{R}_+$, $\int_0^\infty \sigma(m)\,dm = 1$, and let $\mathcal{R}_\diamond = \mathcal{R}_0$ be the basic reproduction number without resistance. With $f(y) = 1 - e^{-y}$, the final cumulative force of infection $z = J(\infty)$ and the final cumulative force of infection of the initial infectives $x = J_0(\infty)$ are linked by

$$
z = F(z) + x, \qquad F(y) = \mathcal{R}_\diamond \int_0^y \sigma(m)\, f(y - m)\,dm .
$$

$F$ is increasing, $F(0) = F'(0) = 0$, $F(y) \to \mathcal{R}_\diamond$ as $y \to \infty$, and $F'(y) = \mathcal{R}_\diamond\int_0^y \sigma(m)e^{m-y}\,dm$.

**Statement.**

1. *Small initial dose.* $(z(x) - x)/x^2 \to \mathcal{R}_\diamond\sigma(0)/2$ as $x \to 0$.
2. *Smooth final size.* If $\mathcal{R}_\diamond \int_0^y \sigma(m)e^{m-y}\,dm < 1$ for all $y \ge 0$, then $z$ is uniquely determined by $x$, is $C^2$, and

    $$
    z'(x) = \Bigl(1 - \mathcal{R}_\diamond\int_0^{z(x)} \sigma(m)e^{m - z(x)}\,dm\Bigr)^{-1},
    $$

    with $z'(0) = 1$, $z'(x) \to 1$ as $x \to \infty$ and $z''(0) = \mathcal{R}_\diamond\sigma(0)$.

3. *Jump.* If $\mathcal{R}_\diamond \int_0^{z_2} \sigma(m)e^{m - z_2}\,dm > 1$ for some $z_2 \ge 0$, then the final size curve $x \mapsto z(x)$ has a discontinuity.
4. *Shape.* $z$ is convex on $[0,m_1]$ if $\sigma$ increases on $[0, z(m_1)]$ (in particular on $[0, m_1 + \mathcal{R}_\diamond]$), and concave on $[m_2,\infty)$ if $\sigma$ vanishes on $[m_2,\infty)$.

So with spread-out resistance the final size depends on the initial dose through a curve that is S-shaped under the conditions of item 4, and that jumps when the slope of $F$ exceeds one somewhere; the borderline case $\max F' = 1$ is left open by the source.

## Depends on

- [Kermack–McKendrick epidemic with dose-threshold resistance](kermack-mckendrick-epidemic-with-dose-threshold-resistance.md)

## Expansion

All statements follow from an abstract analysis of $z = F(z) + x$ with $F$ increasing, $F(0) = 0$, bounded. The minimal solution is continuous where $F' < 1$ along the curve, by the implicit function theorem, giving $z' = 1/(1 - F'(z))$; where $F'$ exceeds one somewhere, the line $z \mapsto z - x$ becomes tangent to $F$ at some $x$ and the minimal root jumps. Convexity of $z$ is inherited from convexity of $F$, which follows from $F'(y) = \mathcal{R}_\diamond\int_0^y \sigma(y-m)e^{-m}\,dm$ when $\sigma$ increases, and concavity from $F'' = \mathcal{R}_\diamond\bigl(\sigma(y) - \int_0^y \sigma(m)e^{m-y}dm\bigr) \le 0$ where $\sigma = 0$.

## Sources

- Joan Ponce and Horst R. Thieme, "A Kermack–McKendrick type epidemic model with double threshold phenomenon (and a possible application to Covid-19)", Journal of Mathematical Biology 92 (2026), 33, <https://doi.org/10.1007/s00285-026-02348-8>; numbering as in arXiv:2409.17278: Section 6, Lemma 6.1 and Theorems 6.2–6.5.

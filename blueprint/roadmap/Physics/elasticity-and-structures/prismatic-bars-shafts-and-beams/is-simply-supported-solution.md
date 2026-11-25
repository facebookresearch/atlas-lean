# Simply supported beam problem under a uniform load

Let $EI$, $L$ and $q$ be real numbers and $w \colon \mathbb{R} \to \mathbb{R}$. The function $w$
solves the simply supported problem if $L > 0$, $w$ is four times continuously differentiable on
$\mathbb{R}$, and

- $EI\, w''''(x) = q$ for every $x \in (0, L)$;
- $w(0) = w(L) = 0$ (zero deflection at both supports);
- $w''(0) = w''(L) = 0$ (zero curvature, hence zero bending moment, at both supports).

This is the Euler–Bernoulli small-deflection model of a prismatic beam of constant bending stiffness
$EI$ on a pin at $x = 0$ and a pin or roller at $x = L$, under the uniform distributed load $q$; the
deflection $w$ and the load $q$ are positive in the same transverse direction. The supports
constrain the deflection, not the slope. No sign is required of $EI$; the model has $EI > 0$, which
the existence and uniqueness results assume.

# Clamped-free cantilever problem under a uniform load and a tip force

Let $EI$, $L$, $q$ and $P$ be real numbers and $w \colon \mathbb{R} \to \mathbb{R}$. The function
$w$ solves the clamped-free cantilever problem if $L > 0$, $w$ is four times continuously
differentiable on $\mathbb{R}$, and

- $EI\, w''''(x) = q$ for every $x \in (0, L)$;
- $w(0) = 0$ and $w'(0) = 0$ (clamped end);
- $EI\, w''(L) = 0$ (zero bending moment at the free end);
- $-EI\, w'''(L) = P$ (the shear force $-EI\, w'''$ at the free end balances the tip force).

This is the Euler–Bernoulli small-deflection model of a prismatic beam of constant bending stiffness
$EI$, clamped at $x = 0$ and free at $x = L$, under the uniform distributed load $q$ and the tip
force $P$; the deflection $w$, the load $q$ and the tip force $P$ are positive in the same
transverse direction. No sign is required of $EI$; the model has $EI > 0$, which the existence and
uniqueness results assume (for $EI = 0$ the conditions force $q = 0$ and $P = 0$).

# Existence of a JKO step on a proper metric space

Let $X$ be a proper metric space (closed balls are compact), $F : X \to \mathbb{R}$ lower
semicontinuous and bounded below by $m$, and $h > 0$. Then from every $x$ there is a
[minimizing-movement step](is-minimizing-movement-step.md). Proof: $G(z) = \tfrac12 d(x, z)^2 + h F(z)$
is lower semicontinuous, and $G(z) \le G(x) = h F(x)$ forces $d(x, z)^2 \le 2h (F(x) - m)$, so the
minimum of $G$ over a compact closed ball is a global minimum.

The Wasserstein space is not proper, and for the Fokker–Planck free energy Jordan, Kinderlehrer
and Otto prove existence (and uniqueness) of the step separately: see
[existence and uniqueness of the JKO step](../jko-scheme/exists-unique-is-jkostep.md).

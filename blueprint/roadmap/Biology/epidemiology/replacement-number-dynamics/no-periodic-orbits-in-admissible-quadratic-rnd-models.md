# Absence of periodic orbits in admissible quadratic replacement number models

**Setting.** Let $\dot X = f(X,I)$, $\dot I = (X-1)I$ be a [replacement number dynamics](replacement-number-dynamics-of-ssiss-models.md) with $f$ at most quadratic in $X$,

$$
f(X,I) = f_0(I) + f_1(I)X + f_2(I)X^2 .
$$

For a choice $\beta_1 > \beta_2$ the corresponding two-susceptible-class model has the form

$$
\dot S_i = (-\beta_i S_i + \gamma_i)I - A_i(I)S_i + A_j(I)S_j - (\beta_i - \beta_j)B(I)S_1S_2, \qquad j \ne i,\quad \gamma_1 + \gamma_2 = 1,
$$

with $B = f_2$ and $A_i(I) = h_f(\beta_i, I)/(\beta_j - \beta_i)$, $h_f(z,I) = P_f(I) + z f_1(I) + z^2\bigl(I + (1-I)f_2(I)\bigr)$, $P_f(I) = (1-I)^{-1}(f_0(I) - f_0(1)I)$. The pair $(\beta_1,\beta_2)$ is *$f$-compatible* if this model is admissible: $\beta_2 \le \beta_1\gamma_1 + \beta_2\gamma_2 \le \beta_1$ and $A_i(I) \ge 0$ for all $I \in [0,1]$. Let $T(\beta)$ be the image of the physical triangle $\{S_1,S_2,I \ge 0,\ S_1 + S_2 + I = 1\}$ in the $(X,I)$ plane.

**Statement.** For every compatible $\beta$, the interior of $T(\beta)$ contains no periodic solutions, homoclinic loops or oriented phase polygons. Since $T(\beta)$ is forward invariant, every forward orbit in its interior converges, by Poincaré–Bendixson, to an equilibrium or to a cycle of equilibria on the boundary.

## Expansion

Use the Busenberg–van den Driessche form of the Bendixson–Dulac criterion on the simplex: for a smooth field $F$ on a neighbourhood of the simplex with $\sum_i F_i = 0$, a Dulac function $u$ with $\nabla\cdot(uF) \le 0$ in the interior and $< 0$ somewhere excludes interior periodic orbits (apply Stokes' theorem to $y \times uF$). Take $y = (S_1,S_2,I)$ and $u = 1/(S_1S_2I)$. Then $\partial(u\dot I)/\partial I = 0$ and

$$
\frac{\partial(u\dot S_i)}{\partial S_i} = -\frac{1}{S_i^2}\left(\frac{\gamma_i}{S_j} + \frac{A_j}{I}\right),
$$

which is negative in the open simplex because admissibility gives $\gamma_i, A_j \ge 0$ (not all zero, since $\gamma_1 + \gamma_2 = 1$).

## Sources

- F. Nill, The replacement number dynamics in SIR-type epidemic models I: From SSISS to RND picture, arXiv:2410.19532 (2024), Corollary 4.1, Lemma 4.7 and Theorem 4.9, <https://doi.org/10.48550/arXiv.2410.19532>.

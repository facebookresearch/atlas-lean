# Direction and reduced stability of the pattern branch

Let $G, H, H_a : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$, $\varphi : \mathbb{R} \to \mathbb{R}$
and real $d_0$, $\sigma$ satisfy:

- **branch:** $\varphi(0) = d_0$, $\varphi$ is continuous at $0$, and for $(a, d)$ near $(0, d_0)$,
  $a\, G(a, d) = 0$ if and only if $a = 0$ or $d = \varphi(a)$;
- **transversal crossing:** $G(0, d_0) = 0$ and $d \mapsto G(0, d)$ has derivative $\sigma > 0$ at
  $d_0$;
- **symmetry to second order:** $G(a, d) = G(0, d) + a^2 H(a, d)$ for $(a, d)$ near $(0, d_0)$, with
  $H$ continuous at $(0, d_0)$ and $c = H(0, d_0) \neq 0$;
- **regularity:** for $(a, d)$ near $(0, d_0)$, $x \mapsto H(x, d)$ has derivative $H_a(a, d)$ at
  $a$, and $H_a$ is continuous at $(0, d_0)$.

Then for every $a \neq 0$ close enough to $0$:

- $c\,(\varphi(a) - d_0) < 0$: the branch bifurcates into $d > d_0$, where $G(0, d) > 0$
  (supercritical), if $c < 0$, and into $d < d_0$ (subcritical) if $c > 0$;
- the map $x \mapsto x\, G(x, \varphi(a))$ has a derivative $\lambda$ at $a$ with $c\, \lambda > 0$:
  the equilibrium $a$ of the reduced equation $\dot a = a\, G(a, d)$ at $d = \varphi(a)$ is linearly
  stable ($\lambda < 0$) exactly when the bifurcation is supercritical.

For a Turing mode $\cos(k_n x)$ with $n \ge 1$ the quadratic term of the reaction projects to zero
on the critical mode, since $\int_0^L \cos^3(k_n x)\, dx = 0$, which motivates the symmetry
hypothesis.

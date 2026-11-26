# Positivity persistence and the origin of dead cores in degenerate chemotaxis

**Model.** Let $\Omega \subset \mathbb{R}^N$ be a bounded smooth domain and $m > 1$. Consider
$$
u_t = \nabla\cdot\big(D(u)\nabla u - uS(u)\nabla v\big) + f(u,v), \qquad v_t = \Delta v + g(u,v), \qquad x\in\Omega,\ t>0,
$$
with no-flux and homogeneous Neumann boundary conditions. Assume:
- $D \in C^0([0,\infty)) \cap C^2((0,\infty))$, $D(0) = 0$, $D' \ge 0$ on $(0,\infty)$, and for some $s_0 \in (0,1]$, $d > 0$, $C_D > 0$: $D(s) \ge d s^{m-1}$ and $sD'(s) \le C_D D(s)$ on $[0,s_0]$ (degenerate, porous-medium-type diffusion);
- $S \in C^2([0,\infty))$ and $f \in C^1([0,\infty)^2)$ nonnegative; $g \in C^1([0,\infty)^2)$ of any sign (e.g. $g = -uv$ for oxygen consumption or $g = u - v$ for signal production);
- $u_0 \in W^{1,\infty}(\Omega)$ nonnegative, $u_0 \not\equiv 0$, compactly supported in $\Omega$; $v_0 \in C^{2+\beta}(\overline\Omega)$ nonnegative, $v_0 \not\equiv 0$, $\partial_\nu v_0 = 0$.

A *dead core* is an open region where the population density vanishes.

**Theorem.** Let $(u,v)$ be a weak solution on $\Omega\times(0,T_0)$ (in the distributional sense with $\Phi(u) = \int_0^u D \in L^1_{\mathrm{loc}}([0,T_0);W^{1,1}(\Omega))$), and assume $u, v \in C^0([0,T_0);L^2(\Omega)) \cap L^\infty(\Omega\times(0,T_0))$. Then for each $T \in (0,T_0)$ there is $\theta \in (0,1)$ with $(u,v) \in C^{\theta,\theta/2}(\overline\Omega\times[0,T]) \times C^{2+\theta,1+\theta/2}(\overline\Omega\times[0,T])$, and whenever $\omega \subset \mathbb{R}^N$ is a smoothly bounded domain and $T \in (0,T_0)$ satisfy
$$ \overline\omega \subseteq \Omega, \qquad u_0 > 0 \text{ in } \overline\omega, \qquad u > 0 \text{ on } \partial\omega\times(0,T), $$
it follows that $u > 0$ in $\overline\omega\times[0,T)$.

Consequently any dead core that appears during the evolution must have grown out of the initial zero set: a "caldera" (a hole opening inside a region of positive density, surrounded by positive density) cannot form. For the prototype $u_t = \nabla\cdot(\nabla u^m - u\nabla v)$, $v_t = \Delta v - uv$ with $m > 1$, a global bounded weak solution with these properties exists, so the conclusion applies to it for all times.

## Expansion

Where $u > 0$ the equation is uniformly parabolic, so $u$ is classical there. On $\overline\omega$ the hypotheses give a positive lower bound on the parabolic boundary of $\omega\times(0,T)$; the drift term involves $\nabla v$, which is bounded thanks to the Hölder regularity of $v$. Comparing with a subsolution built from the porous-medium structure ($D(s) \ge ds^{m-1}$, $sD' \le C_D D$) shows that $u$ cannot touch zero at a first interior time, since at such a point the diffusion, drift, and nonnegative source $f$ cannot drive the minimum down. This is a strong-minimum-principle analogue for degenerate diffusion, which in general lacks one.

## Sources

- Tobias Black, "Avoidance of caldera-type dead cores in a chemotaxis system with degenerate diffusion and compactly supported initial population density", arXiv:2608.16703 (2026), Section 1, Definition 1.1, Theorems 1.2 and 1.3; Section 2, <https://doi.org/10.48550/arXiv.2608.16703>.

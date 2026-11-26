# Stabilization of weakly singular chemotaxis with logistic source

**Model.** In a smooth bounded convex domain $\Omega \subset \mathbb R^n$, $n \ge 2$, with homogeneous Neumann conditions,
$$u_t = \Delta u - \chi\,\nabla\cdot\Big(\frac{u}{v^{\alpha}}\nabla v\Big) + r u - \mu u^2, \qquad 0 = \Delta v - v + u,$$
with weakly singular sensitivity exponent $\alpha \in (0,1)$, $\chi, r, \mu > 0$, and non-negative, nontrivial initial cell density. The spatially homogeneous steady state is $(u,v) = (r/\mu, r/\mu)$.

**Theorem (eventual bound).** If $\alpha \in \big(0,\frac{n+2}{2n}\big)$ and $\mu > \mu_0$ for a suitably large $\mu_0$, the system has a globally bounded classical solution, and there are $t_0>0$ and $L_0 = L_0(\chi,\alpha,r,\Omega)$ independent of $\mu$ with
$$\|u(\cdot,t)\|_{L^\infty(\Omega)} \le \frac{L_0}{\mu}, \qquad t > t_0.$$
No uniform positive lower bound on $v$ is needed.

**Theorem (convergence).** If $\alpha \in (0,\tfrac12)$, there is $\mu_\star > 0$ such that for $\mu > \mu_\star$,
$$\Big\|u - \frac r\mu\Big\|_{L^\infty(\Omega)} + \Big\|v - \frac r\mu\Big\|_{L^\infty(\Omega)} \to 0 \qquad (t\to\infty).$$
If moreover $\alpha \in \big(0,\frac{n+2}{n^2+4}\big)$, the convergence is exponential: the left side is at most $L_\star e^{-\eta_\star t}$ with $\eta_\star = \eta_\star(r) > 0$.

## Expansion

The substitution $z = v^{1-\alpha}$ removes the singularity, turning the sensitivity $u v^{-\alpha}\nabla v$ into $\frac{u}{1-\alpha}\nabla z$ at the price of a nonlinear elliptic equation for $z$. Strong logistic damping ($\mu$ large) gives the explicit eventual $L^\infty$ bound of order $1/\mu$; convergence then follows from an energy functional of the form $\int (u - \tfrac r\mu - \tfrac r\mu\ln\tfrac{\mu u}{r})$, whose dissipation dominates the chemotactic cross term once $\mu$ is large, and the smaller range of $\alpha$ makes the dissipation coercive enough for an exponential rate.

## Sources

- Xiangdong Zhao, "Long-time behavior of solution to a chemotaxis system with weakly singular sensitivity and logistic source", arXiv:2608.08087 (2026), Theorems 1 and 2, <https://doi.org/10.48550/arXiv.2608.08087>.

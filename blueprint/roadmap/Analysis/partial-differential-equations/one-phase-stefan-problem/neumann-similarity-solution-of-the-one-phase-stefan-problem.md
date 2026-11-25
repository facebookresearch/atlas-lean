# Neumann similarity solution of the one-phase Stefan problem

This node covers the similarity solution of one-dimensional melting. Let a material at its melting temperature $T_m$ occupy $x > 0$,
and at $t = 0$ let the face $x = 0$ be held at $T_w > T_m$. With conductivity $k > 0$, density $\rho > 0$, specific heat
$c > 0$, thermal diffusivity $\alpha = k/(\rho c)$ and latent heat $\mathcal{L} > 0$, consider the liquid region $0 < x < s(t)$ with

$$T_t = \alpha T_{xx}, \quad T(0, t) = T_w, \quad T(s(t), t) = T_m, \quad \rho\mathcal{L}\,s'(t) = -k\,T_x(s(t), t), \quad s(0) = 0 .$$

Let $\mathrm{St} = c(T_w - T_m)/\mathcal{L}$. The equation $\lambda e^{\lambda^2}\operatorname{erf}(\lambda) = \mathrm{St}/\sqrt\pi$ has exactly one root
$\lambda > 0$, and $s(t) = 2\lambda\sqrt{\alpha t}$ with
$T(x, t) = T_w - (T_w - T_m)\operatorname{erf}\!\big(x/(2\sqrt{\alpha t})\big)/\operatorname{erf}(\lambda)$ is a classical solution for $t > 0$.

## Expansion

A good expansion verifies the profile and the Stefan condition, and proves existence and uniqueness of $\lambda$ from the strict
monotonicity of $\lambda \mapsto \lambda e^{\lambda^2}\operatorname{erf}(\lambda)$ from $0$ to $\infty$. Uniqueness of the free-boundary solution
in a stated class, the two-phase problem and boiling or condensation correlations are separate nodes.

## Sources

- J. Crank, *Free and Moving Boundary Problems*, Oxford University Press, 1984, for the Neumann solution.
- J. H. Lienhard IV and J. H. Lienhard V, *A Heat Transfer Textbook*, 3rd edition, Phlogiston Press, 2001, for phase-change heat transfer.

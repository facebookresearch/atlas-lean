# Cahn–Hilliard model of tumor growth

Let $\Omega \subset \mathbb{R}^d$ be a bounded domain with smooth boundary and let $\varphi(x, t) \in [0, 1]$ be the tumor volume fraction ($\varphi = 1$ tumor, $\varphi = 0$ healthy tissue). Given an interface parameter $\varepsilon > 0$ and a double-well potential $\Psi$ with minima at $0$ and $1$, for example $\Psi(\varphi) = \frac14 \varphi^2 (1-\varphi)^2$, the Ginzburg–Landau energy is

$$E(\varphi) = \int_\Omega \left(\Psi(\varphi) + \frac{\varepsilon^2}{2} |\nabla \varphi|^2\right) dx.$$

The Cahn–Hilliard equation with mobility $m(\varphi) \ge 0$ (typically $m(\varphi) = M\varphi^2(1-\varphi)^2$ with $M > 0$) is

$$\partial_t \varphi = \operatorname{div}\big(m(\varphi) \nabla \mu\big), \qquad \mu = \Psi'(\varphi) - \varepsilon^2 \Delta \varphi \quad \text{in } \Omega \times (0, T),$$

with no-flux boundary conditions $\partial_n \varphi = 0$ and $m(\varphi)\partial_n \mu = 0$ on $\partial\Omega$. For sufficiently smooth solutions:

1. Mass is conserved: $\frac{d}{dt}\int_\Omega \varphi\, dx = 0$.
2. Energy is dissipated: $\frac{d}{dt} E(\varphi(t)) = -\int_\Omega m(\varphi) |\nabla \mu|^2\, dx \le 0$.

Tumor-growth models replace the equation by $\partial_t\varphi + \operatorname{div}(\varphi v) = \operatorname{div}\big(m(\varphi)\nabla\mu\big) + S$, with a velocity field $v$ and a net source $S$ (proliferation minus apoptosis, depending on nutrients), and keep $\mu$ as the variational derivative of $E$; they do not keep the two identities above. On an impermeable boundary, $v \cdot n = 0$ on $\partial\Omega$, the conservative advection term does not change the total mass, and only the source does: $\frac{d}{dt}\int_\Omega \varphi\, dx = \int_\Omega S\, dx$. The energy balance becomes $\frac{d}{dt} E(\varphi(t)) = -\int_\Omega m(\varphi)|\nabla\mu|^2\, dx + \int_\Omega \mu S\, dx + \int_\Omega \varphi\, v \cdot \nabla\mu\, dx$; even at $v = 0$ the source contributes $\int_\Omega \mu S\, dx$, which has no fixed sign, so the forced model need not dissipate $E$. With constant mobility the problem is well posed under suitable assumptions; uniqueness for degenerate mobility is open.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Integral balance in divergence form](../../../Analysis/ordinary-differential-equations/mechanical-and-engineering-models/continuum-balances/has-deriv-at-set-integral-of-divergence.md)

## Expansion

The equation is the mass balance $\partial_t \varphi = -\operatorname{div} J$ with flux $J = -m(\varphi)\nabla\mu$, where $\mu$ is the Gâteaux derivative of $E$: for a test function $\eta$, $\frac{d}{ds}E(\varphi + s\eta)|_{s=0} = \int_\Omega (\Psi'(\varphi)\eta + \varepsilon^2 \nabla\varphi \cdot \nabla\eta)\, dx = \int_\Omega (\Psi'(\varphi) - \varepsilon^2\Delta\varphi)\eta\, dx$ using $\partial_n\varphi = 0$. Integrating the equation over $\Omega$ and using the no-flux condition gives mass conservation; with advection and a source, the same integral balance gives $\int_\Omega S\,dx$, since $\int_\Omega \operatorname{div}(\varphi v)\,dx = \int_{\partial\Omega}\varphi\, v\cdot n = 0$. For the energy, $\frac{d}{dt}E = \int_\Omega \mu\, \partial_t\varphi\, dx = \int_\Omega \mu\, \operatorname{div}(m(\varphi)\nabla\mu)\, dx = -\int_\Omega m(\varphi)|\nabla\mu|^2\, dx$ after integration by parts; in the forced model $\int_\Omega \mu\,S\,dx$ and $-\int_\Omega \mu \operatorname{div}(\varphi v)\,dx = \int_\Omega \varphi\, v\cdot\nabla\mu\,dx$ are added. The double well drives phase separation into tumor and healthy regions, and the gradient term penalizes interface area, giving the interface a width of order $\varepsilon$.

## Sources

- M. Fritz, Tumor evolution models of phase-field type with nonlocal effects and angiogenesis, *Bull. Math. Biol.* 85 (2023), 44, <https://doi.org/10.1007/s11538-023-01151-6> (Section 2.1, Equations 2.1–2.2).
- J. W. Cahn and J. E. Hilliard, Free energy of a nonuniform system. I. Interfacial free energy, *J. Chem. Phys.* 28 (1958), 258–267, <https://doi.org/10.1063/1.1744102>.

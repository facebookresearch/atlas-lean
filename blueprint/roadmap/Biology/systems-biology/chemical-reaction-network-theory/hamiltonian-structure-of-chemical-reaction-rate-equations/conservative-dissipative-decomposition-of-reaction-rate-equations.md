# Conservative–dissipative decomposition of non-equilibrium reaction rate equations

**Setting.** A reaction network with $N$ species and $M$ reversible reactions $j$ (stoichiometric change $\nu_j \in \mathbb{Z}^N$) in a container of volume $V$ is modeled by a random time-changed Poisson process for the concentrations $X^V(t) = (\text{molecule counts})/V$ with mesoscopic mass-action propensities. As $V \to \infty$ the law of large numbers gives the **reaction rate equation** (RRE)

$$\dot x = \sum_{j=1}^M \nu_j\big(\Phi^+_j(x) - \Phi^-_j(x)\big), \qquad \Phi^\pm_j(x) = k^\pm_j\prod_{\ell=1}^N x_\ell^{\nu^\pm_{j\ell}},$$

and the WKB ansatz $p(x,t) \approx e^{-V\psi(x,t)}$ for the chemical master equation yields the Hamilton–Jacobi equation $\partial_t\psi + H(\nabla\psi, x) = 0$ with the convex Hamiltonian

$$H(p,x) = \sum_{j=1}^M\Big(\Phi^+_j(x)\big(e^{\nu_j\cdot p} - 1\big) + \Phi^-_j(x)\big(e^{-\nu_j\cdot p} - 1\big)\Big).$$

Then $H(0,x) = 0$, the RRE is $\dot x = \nabla_pH(0,x)$, and the Legendre dual $L$ of $H$ is the large-deviation action of the process.

**Theorem (decomposition).** Let $H$ be convex with $H(0,x) = 0$ and let $\psi^{ss}$ be a steady solution, $H(\nabla\psi^{ss}(x), x) = 0$ (for example the limit $-\lim_{V\to\infty} V^{-1}\log\pi_V$ of a positive invariant measure). Then the RRE splits as

$$\dot x = W(x) - K(x)\nabla\psi^{ss}(x), \qquad W(x) = \int_0^1 \nabla_pH(\theta\nabla\psi^{ss}(x), x)\,d\theta, \qquad K(x) = \int_0^1 (1-\theta)\,\nabla^2_{pp}H(\theta\nabla\psi^{ss}(x), x)\,d\theta,$$

where

1. the conservative part is orthogonal to the energy gradient, $\langle W(x), \nabla\psi^{ss}(x)\rangle = 0$, so $W = \mathcal{A}\nabla\psi^{ss}$ with the antisymmetric operator $\mathcal{A} = (W\otimes\nabla\psi^{ss} - \nabla\psi^{ss}\otimes W)/|\nabla\psi^{ss}|^2$;
2. $K(x)$ is symmetric nonnegative definite, so for every increasing $\phi$,

$$\frac{d}{dt}\phi(\psi^{ss}(x(t))) = -\phi'(\psi^{ss})\,\langle K\nabla\psi^{ss}, \nabla\psi^{ss}\rangle \le 0,$$

and $\psi^{ss}$ is a Lyapunov function for the RRE (a GENERIC-type structure).

For the chemical Hamiltonian, the minimizer of the dynamic solution $\psi(\cdot,t)$ is the RRE solution started at the minimizer of $\psi_0$.

**Entropy production.** The total entropy production rate splits into non-adiabatic and adiabatic (housekeeping) parts, both nonnegative:

$$T\dot S_{\mathrm{na}} = k_BT\,\langle K(x)\nabla\psi^{ss}, \nabla\psi^{ss}\rangle, \qquad T\dot S_{\mathrm{a}} = k_BT\sum_j\Big[\mathrm{KL}\big(\Phi^+_j \,\|\, \Phi^-_je^{-\nu_j\cdot\nabla\psi^{ss}}\big) + \mathrm{KL}\big(\Phi^-_j \,\|\, \Phi^+_je^{\nu_j\cdot\nabla\psi^{ss}}\big)\Big].$$

## Expansion

Since $H(0,x) = 0 = H(\nabla\psi^{ss},x)$, Taylor expansion along the segment $\theta\nabla\psi^{ss}$ gives $0 = \langle\int_0^1\nabla_pH(\theta\nabla\psi^{ss})\,d\theta, \nabla\psi^{ss}\rangle$, which is the orthogonality of $W$; the identity $\nabla_pH(0,x) = W - K\nabla\psi^{ss}$ is the integral form of Taylor's theorem with remainder, and convexity of $H$ makes $K \ge 0$. When the network satisfies detailed balance, $H(p,x) = H(\nabla\psi^{ss} - p, x)$ is symmetric, $W$ vanishes and the RRE becomes a strong gradient flow of $\psi^{ss}$ in a non-quadratic metric; for open systems coupled to chemostats the conservative part $W$ carries the non-equilibrium circulation, and the adiabatic entropy production measures the energy needed to sustain it.

## Sources

- Yuan Gao and Jian-Guo Liu, "Revisit of macroscopic dynamics for some non-equilibrium chemical reactions from a Hamiltonian viewpoint", arXiv:2108.05396 (2021), Section 2 (RRE, WKB and Theorems 2.6–2.7), Theorem 3.2, Corollary 3.5, Propositions 3.7 and 3.8, Section 4 (symmetric Hamiltonians), <https://doi.org/10.48550/arXiv.2108.05396>. Published version: J. Stat. Phys. 189 (2022) 22, <https://doi.org/10.1007/s10955-022-02985-5>.

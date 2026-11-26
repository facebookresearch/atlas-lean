# Global nonnegative weak solutions of the traction-driven Cahn–Hilliard model

Consider the one-sided degenerate Cahn–Hilliard model with anisotropic traction, $\partial_t\rho=\operatorname{div}J$, $J=\rho\nabla q+\kappa\rho D(\nu)\nabla\rho$, $q=\varepsilon^{-1}W'(\rho)-\varepsilon\Delta\rho$, $\kappa=\varepsilon^{-1}\eta^2$, with no-flux boundary conditions. Assume:

1. $\Omega\subset\mathbb R^d$, $d\in\{2,3\}$, is bounded with $C^{1,1}$ boundary, and $T>0$;
2. $\varepsilon>0$, $\eta\ge0$;
3. $\rho_0\in H^1(\Omega)$, $\rho_0\ge0$ a.e., and $E(\rho_0)<\infty$;
4. $D(\nu)\in L^\infty(\Omega\times(0,T);\mathbb R^{d\times d})$ is symmetric with $0\le\xi^\top D(\nu)\xi\le\Lambda|\xi|^2$ for some $\Lambda>0$;
5. $W\in C^2(\mathbb R)$ with $W(s)\ge c_0|s|^p-c_1$, $W''(s)\ge-c_1$, $|W'(s)|\le C_W(1+|s|^{p-1})$ and $|W''(s)|\le C_W(1+|s|^{p-2})$, where $2<p<\infty$ if $d=2$ and $2<p\le4$ if $d=3$.

**Theorem (global existence).** There is a weak solution $(\rho,J)$ on $(0,T)$ with

$$\rho\in L^\infty(0,T;H^1(\Omega))\cap L^2(0,T;H^2(\Omega))\cap C([0,T];L^2(\Omega)),\qquad \rho\ge0\ \text{a.e.},$$

$\partial_t\rho\in L^{16/9}(0,T;(W^{1,16/7}(\Omega))')$, $J\in L^{16/9}(\Omega\times(0,T);\mathbb R^d)$ and $\rho(0)=\rho_0$, such that:

- **mass is conserved:** $\int_\Omega\rho(t)\,dx=\int_\Omega\rho_0\,dx$ for all $t\in[0,T]$;
- **energy inequality:** with the diffusive flux $J^{\mathrm{diff}}=J-\kappa\rho D(\nu)\nabla\rho$, for a.e. $t$,

$$E(\rho(t))+\frac12\int_0^t\!\!\int_\Omega\frac{|J^{\mathrm{diff}}|^2}{\rho}\,dx\,ds\le E(\rho_0)+C(\Lambda)\kappa^2\int_0^t\!\!\int_\Omega\rho|\nabla\rho|^2\,dx\,ds;$$

- **entropy inequality:** with $\Phi(s)=s\log s-s+1$ ($\Phi(0)=1$), for a.e. $t$,

$$\int_\Omega\Phi(\rho(t))\,dx+\varepsilon\int_0^t\!\!\int_\Omega|\Delta\rho|^2+\kappa\int_0^t\!\!\int_\Omega\nabla\rho\cdot D(\nu)\nabla\rho\le\int_\Omega\Phi(\rho_0)\,dx+\frac{c_1}{\varepsilon}\int_0^t\!\!\int_\Omega|\nabla\rho|^2 .$$

## Depends on

- [One-sided degenerate Cahn–Hilliard model with anisotropic traction](one-sided-degenerate-cahn-hilliard-model-with-anisotropic-traction.md)

## Expansion

The proof regularizes the mobility to $m_{\delta,L}$ (bounded below by $\delta$, truncated at level $L$) and truncates the potential to $W_L$ with $L$-uniform growth and coercivity bounds, solves the uniformly parabolic problem by Galerkin approximation, and tests with the chemical potential to get the energy inequality, controlling the traction cross term by Young's inequality and $D(\nu)\le\Lambda I$. The key step tests with the mobility-matched entropy variable $\Phi'(\rho)=\log\rho$: since $\nabla\Phi'(\rho)=\nabla\rho/\rho$ cancels the mobility, the traction flux turns into the coercive term $\kappa\int\nabla\rho\cdot D(\nu)\nabla\rho$ and the fourth-order term into $\varepsilon\int|\Delta\rho|^2$, while $W''\ge-c_1$ handles the potential. The entropy bound gives $L^2(H^2)$ control and non-negativity as $\delta\to0$; the energy bound gives the weighted control of $J^{\mathrm{diff}}$. Compactness (Aubin–Lions type) then allows $\delta\to0$ for fixed $L$ and finally $L\to\infty$.

## Sources

- M. Fritz, *Global weak solutions of a one-sided degenerate Cahn–Hilliard model for traction-driven digit morphogenesis*, arXiv:2606.10793 (2026), Assumption 3.1, Definition 3.2, Theorem 3.5 and its proof (Lemmas 3.6–3.9). <https://doi.org/10.48550/arXiv.2606.10793>

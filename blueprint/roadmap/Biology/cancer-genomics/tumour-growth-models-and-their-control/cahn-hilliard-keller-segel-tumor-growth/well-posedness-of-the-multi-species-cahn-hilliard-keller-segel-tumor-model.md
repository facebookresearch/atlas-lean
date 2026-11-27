# Well-posedness of the multi-species Cahn–Hilliard–Keller–Segel tumor model

**Model.** On a bounded smooth domain $\Omega \subset \mathbb{R}^2$ with $Q = \Omega \times (0,T)$, let $\phi$ be the tumor-cell phase variable, $\mu$ its chemical potential, $a$ the volume fraction of tumor-induced vasculature, $n$ a nutrient and $\sigma$ an angiogenic signal. With a distributed control $u$ acting as a source of vasculature,

$$
\begin{aligned}
&\partial_t \phi - \Delta\mu + \chi_\phi \Delta n = -m\phi + h(\phi), \qquad -\Delta\phi + F'(\phi) = \mu,\\
&\partial_t a - \Delta a + \chi_a \nabla\cdot(a\nabla\sigma) = a - a^2 + u,\\
&\partial_t n - \Delta n - \chi_\phi\, n = c_\phi \phi + c_n n + c_\sigma \sigma + c_0, \qquad \partial_t \sigma - \Delta\sigma - \chi_a\, a = 1 - \sigma - a\sigma,
\end{aligned}
$$

with homogeneous Neumann conditions for all five variables and initial data $\phi_0, a_0, n_0, \sigma_0$. The system comes from the free energy $\int_\Omega [a(\ln a - 1) - \chi_\phi n\phi - \chi_a a\sigma + \frac12|\nabla n|^2 + \frac12|\nabla\sigma|^2 + \frac12|\nabla\phi|^2 + F(\phi)]$, coupling Cahn–Hilliard phase separation of the tumor with Keller–Segel chemotaxis of the vasculature.

**Hypotheses.** $m > 0$, $\chi_\phi, \chi_a \in (0,1)$, $c_\phi, c_n, c_\sigma, c_0 \in \mathbb{R}$, $h \in W^{2,\infty}(\mathbb{R})$. The potential $F = F_1 + F_2$ has domain $\mathbb{R}$ or $(0,1)$, with $F_1$ convex, $F_2'$ Lipschitz, both $C^4$; if the domain is $\mathbb{R}$ then $F(r)/r^2 \to \infty$ as $|r| \to \infty$, and if it is $(0,1)$ then $F'(r) \to \mp\infty$ at $0$ and $1$ with $|F_1''(r)| \le e^{C_F(|F_1'(r)| + 1)}$. This covers the double-well $\frac{c_1}{4}r^2(r-1)^2$ and the logarithmic potential $r\ln r + (1-r)\ln(1-r) + c_2 r(1-r)$. The control satisfies $0 \le u \le u_{\max}$ a.e. with $u_{\max} \in L^\infty(Q)$. The initial data are regular ($\phi_0 \in H^3$ or $H^4$ depending on $F$, Neumann-compatible, with values in the domain of $F$ together with explicit bounds $\pm R$ determined by $h$ and $m$; $a_0 \in H^1$, $a_0 > 0$; $n_0, \sigma_0 \in H^2$ with Neumann data and $0 \le \sigma_0 \le 1$).

**Theorem (well-posedness, stability, separation).** Under these hypotheses there is a unique strong solution $(\phi,\mu,a,n,\sigma)$ in the regularity class of the paper. Moreover

$$
\|(\phi,\mu,a,n,\sigma)\|_{\mathcal{Y}} \le K_1, \qquad r_- \le \phi \le r_+ \ \text{ a.e. in } Q,
$$

with constants $K_1 > 0$ and $r_\pm$ in the domain of $F$ that depend only on $\Omega$, $T$, the structure, the initial data and $u_{\max}$, and not on $u$. In particular, for the logarithmic potential, $\phi$ stays strictly away from the pure phases $0$ and $1$.

**Theorem (continuous dependence).** If $u_1, u_2$ are two admissible controls with solutions $(\phi_i,\mu_i,a_i,n_i,\sigma_i)$, then

$$
\|\phi_1 - \phi_2\| + \|\mu_1 - \mu_2\|_{L^2(0,T;H^1)} + \|a_1 - a_2\| + \|n_1 - n_2\| + \|\sigma_1 - \sigma_2\| \le K_2\, \|u_1 - u_2\|_{L^2(Q)},
$$

where the norms on $\phi$, $a$, $n$, $\sigma$ are the energy-type norms of the paper (for instance $H^1(0,T;H^{-1}) \cap L^\infty(0,T;H^1) \cap L^2(0,T;H^2)$ for $\phi$) and $K_2$ depends only on the same data.

## Expansion

Existence builds on the regularity theory for this system in two space dimensions; the key extra steps are uniform-in-$u$ estimates and a separation property for $\phi$. The logistic term $a - a^2$ prevents chemotactic blow-up of $a$, and the bounds $0 \le \sigma \le 1$, $a \ge 0$ follow from comparison. Two-dimensional Sobolev embeddings make $a$ and $\nabla\sigma$ belong to $L^4$, so the chemotactic flux $a\nabla\sigma$ is well defined, and $\nabla\phi \in L^\infty(Q)$. Separation $r_- \le \phi \le r_+$ is obtained by testing with truncations, using the growth condition on $F_1''$ in the singular case; it makes $F$ and its derivatives bounded along solutions, which is what the Lipschitz estimate of the continuous-dependence theorem and the later control analysis need.

## Sources

- Pierluigi Colli, Gianni Gilardi, Andrea Signori, Jürgen Sprekels, "Solvability and optimal control of a multi-species Cahn–Hilliard–Keller–Segel tumor growth model", ESAIM: Control, Optimisation and Calculus of Variations 31 (2025), 85, <https://doi.org/10.1051/cocv/2025070>. Published version of arXiv:2407.18162, cited next; locators there refer to the arXiv version.
- Pierluigi Colli, Gianni Gilardi, Andrea Signori, Jürgen Sprekels, "Solvability and optimal control of a multi-species Cahn-Hilliard-Keller-Segel tumor growth model," arXiv 2024. Section 2, Theorem 2.2 (well-posedness, stability and separation) and Theorem 2.3 (continuous dependence); Sections 3–4 (proofs). <https://doi.org/10.48550/arXiv.2407.18162>

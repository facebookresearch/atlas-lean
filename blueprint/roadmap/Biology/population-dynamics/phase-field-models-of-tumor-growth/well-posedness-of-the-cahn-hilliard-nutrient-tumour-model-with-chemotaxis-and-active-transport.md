# Well-posedness of the Cahn-Hilliard-nutrient tumour model with chemotaxis and active transport

**Model.** Let $\Omega \subset \mathbb{R}^d$ be a bounded Lipschitz domain with boundary $\Gamma$ and outer normal $\nu$. The order parameter $\varphi$ ($\varphi = 1$ tumour, $\varphi = -1$ healthy tissue), chemical potential $\mu$ and nutrient concentration $\sigma$ satisfy

$$
\begin{aligned}
\partial_t \varphi &= \operatorname{div}\big(m(\varphi) \nabla \mu\big) + (\lambda_p \sigma - \lambda_a)\, h(\varphi),\\
\mu &= A\, \Psi'(\varphi) - B\, \Delta \varphi - \chi_\varphi\, \sigma,\\
\partial_t \sigma &= \operatorname{div}\big(n(\varphi)(\chi_\sigma \nabla \sigma - \chi_\varphi \nabla \varphi)\big) - \lambda_c\, \sigma\, h(\varphi),
\end{aligned}
$$

in $\Omega \times (0, T)$, with $\nabla\varphi \cdot \nu = \nabla \mu \cdot \nu = 0$ and the Robin nutrient supply $n(\varphi)\chi_\sigma \nabla \sigma \cdot \nu = K(\sigma_\infty - \sigma)$ on $\Gamma$. Here $\lambda_p$ (proliferation), $\lambda_a$ (apoptosis), $\lambda_c$ (consumption), $\chi_\varphi$ (chemotaxis and active transport) are non-negative, and $\chi_\sigma, A, B, K > 0$. The term $-\chi_\varphi \sigma$ in $\mu$ drives tumour cells up nutrient gradients (chemotaxis); the term $-\chi_\varphi \nabla \varphi$ in the nutrient flux transports nutrient towards the tumour (active transport).

**Hypotheses.** $\varphi_0 \in H^1$, $\sigma_0 \in L^2$, $\sigma_\infty \in L^2(0,T; L^2(\Gamma))$; the mobilities and interpolation function are continuous with $m_0 \le m \le m_1$, $n_0 \le n \le n_1$, $0 \le h \le h_\infty$; the potential $\Psi \in C^{1,1}(\mathbb{R})$ is non-negative with $\Psi(t) \ge R_1 |t|^2 - R_2$ and $|\Psi'(t)| \le R_3(1 + |t|)$, and the cross-diffusion is dominated by the potential:

$$
A > \frac{2 \chi_\varphi^2}{\chi_\sigma R_1}.
$$

**Theorem (global weak solutions).** For every $T > 0$ there exists a weak solution with

$$
\varphi \in L^\infty(0,T; H^1) \cap H^1(0,T; (H^1)^*), \quad \mu \in L^2(0,T; H^1), \quad \sigma \in L^2(0,T; H^1) \cap L^\infty(0,T; L^2) \cap H^1(0,T; (H^1)^*).
$$

**Theorem (continuous dependence and uniqueness).** If $d \le 4$, $h$ is Lipschitz and $m \equiv n \equiv 1$, then two weak solutions with data $(\varphi_{0,i}, \sigma_{0,i}, \sigma_{\infty,i})$ satisfy

$$
\sup_{s \le T}\big(\|\sigma_1 - \sigma_2\|_{L^2}^2 + \|\varphi_1 - \varphi_2\|_{L^2}^2\big) + \|\mu_1 - \mu_2\|_{L^2(L^2)}^2 + \|\nabla(\sigma_1 - \sigma_2)\|_{L^2(L^2)}^2 + \|\nabla(\varphi_1 - \varphi_2)\|_{L^2(L^2)}^2 \le C\big(\|\sigma_{0,1} - \sigma_{0,2}\|_{L^2}^2 + \|\varphi_{0,1} - \varphi_{0,2}\|_{L^2}^2 + \|\sigma_{\infty,1} - \sigma_{\infty,2}\|_{L^2(L^2(\Gamma))}^2\big),
$$

with $C$ depending on $\|\sigma_i\|_{L^\infty(L^2)}$, $T$ and the parameters; in particular weak solutions are unique. The quasi-static variant, where the nutrient equation is replaced by its elliptic version $-\operatorname{div}(D(\varphi)(\nabla \sigma - \eta \nabla \varphi)) + \lambda_c \sigma h(\varphi) = 0$, has global weak solutions for every $A > 0$ (no smallness condition) and the analogous continuous dependence estimate.

## Expansion

Without source terms the system dissipates a Ginzburg-Landau energy built from $A\Psi(\varphi) + \tfrac{B}{2}|\nabla\varphi|^2$ and a quadratic nutrient part, but the source terms $(\lambda_p\sigma - \lambda_a)h(\varphi)$ break the usual Lyapunov structure, and testing the $\varphi$-equation with $\mu$ produces a term $\int (\lambda_p \sigma - \lambda_a) h(\varphi)\mu$ with no sign. The proof controls the mean of $\mu$ via the equation for $\mu$ tested with $1$, then uses the quadratic lower bound on $\Psi$ and the condition $A > 2\chi_\varphi^2/(\chi_\sigma R_1)$ to absorb the cross term $\chi_\varphi \sigma \varphi$ into the potential and nutrient energies; a Gronwall inequality in integral form closes the a priori bound. Existence follows by Galerkin approximation and Aubin-Lions compactness. For continuous dependence, the differences are tested against the inverse Neumann Laplacian of $\varphi_1 - \varphi_2$, and the restriction $d \le 4$ comes from the embedding $H^1 \subset L^4$ used to bound the products of differences.

## Proof depends on

- [Gronwall inequality in integral form](../../../Analysis/ordinary-differential-equations/gronwall-inequality/gronwall-inequality-integral-form.md)

## Sources

- Harald Garcke and Kei Fong Lam, "Well-posedness of a Cahn--Hilliard system modelling tumour growth with chemotaxis and active transport", arXiv (2015), Assumption 2.1, Theorem 2.1 (global weak solutions), Theorem 2.2 (continuous dependence), Theorems 2.3 and 2.4 (quasi-static nutrient), Lemma 3.2 (a priori estimate), <https://doi.org/10.48550/arXiv.1511.06143>.

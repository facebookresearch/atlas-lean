# Stability of equilibria in the HIV model with logistic T-cell growth and viral diffusion

**Model.** On the square $\Omega_\ell = (0,\ell)^2$ with periodic boundary conditions for the virus, consider uninfected CD4 T cells $T$, infected T cells $I$ and free virus $V$:

$$\frac{\partial T}{\partial t} = \alpha - \mu_T T + rT\Big(1 - \frac{T}{T_{\max}}\Big) - \gamma VT, \qquad \frac{\partial I}{\partial t} = \gamma VT - \mu_I I, \qquad \frac{\partial V}{\partial t} = N\mu_I I - \mu_V V + d_V \Delta V.$$

Only the virus diffuses. The parameters $\alpha, \gamma, \mu_T, \mu_I, \mu_V, d_V$ are fixed positive numbers with $\mu_I > \mu_T$; the burst size $N > 0$ and the logistic proliferation rate $r \ge 0$ are the bifurcation parameters; and $T_{\max}$ is taken large compared with every combination of the other parameters of the same dimension (in particular $T_{\max} > \alpha/\mu_T$). The net proliferation rate $r - \mu_T$ may have either sign.

**Equilibria and threshold.** Put

$$T_0(r) = \frac{r - \mu_T + \sqrt{(r - \mu_T)^2 + 4\alpha r/T_{\max}}}{2r}\, T_{\max}, \qquad R_0(N, r) = \frac{\gamma N T_0(r)}{\mu_V}.$$

The uninfected steady state is $\mathbf{X}_u = (T_0, 0, 0)$; the infected steady state is spatially constant,

$$T_i = \frac{\mu_V}{\gamma N}, \qquad V_i = \frac{\alpha N}{\mu_V} - \frac{\mu_T}{\gamma} + \frac{r}{\gamma}\Big(1 - \frac{\mu_V}{\gamma N T_{\max}}\Big), \qquad I_i = \frac{\mu_V}{N\mu_I}V_i.$$

Let $\mathcal{U} = \{(N,r) : R_0 < 1\}$ and $\mathcal{I} = \{(N,r) : R_0 > 1\}$; their interface is the decreasing curve $N = N_{\mathrm{crit}}(r) = \mu_V/(\gamma T_0(r))$.

**Theorem (equilibria).** In $\mathcal{U}$ the uninfected state $\mathbf{X}_u$ is the only non-negative equilibrium; in $\mathcal{I}$ there are exactly two, $\mathbf{X}_u$ and $\mathbf{X}_i$. Moreover $0 < T_u < T_{\max}$, and $0 < T_i < T_{\max}$ in $\mathcal{I}$.

**Theorem (uninfected state).** $\mathbf{X}_u$ is asymptotically stable in $\mathcal{U}$ and unstable in $\mathcal{I}$.

**Theorem (infected state).** For $T_{\max}$ large enough there is a closed unbounded set $\mathcal{P} \subset \mathcal{I}$, of the form $\mathcal{P} = \{(N,r) : N \ge N_{2,0},\ r_{1,0}(N) \le r \le r_{2,0}(N)\}$, on which the second Hurwitz determinant of the spatially homogeneous (zero-mode) characteristic polynomial is non-positive, such that $\mathbf{X}_i$ is asymptotically stable for $(N,r) \in \mathcal{I} \setminus \mathcal{P}$ and unstable in the interior of $\mathcal{P}$.

So the stability of the infected state is decided by the zero Fourier mode, exactly as in the model without diffusion: viral diffusion does not enlarge the stability region.

## Expansion

The linearization at an equilibrium is a sectorial operator on $(L^2)^3$ generating an analytic semigroup, so the linearized stability principle applies. Expanding the resolvent equation in the Fourier modes of the periodic Laplacian, with eigenvalues $-\lambda_k$, $\lambda_k = 4\pi^2(k_1^2 + k_2^2)/\ell^2$, reduces the spectrum to the roots of a family of cubic polynomials, one per mode, in which $d_V\lambda_k$ is added to the viral clearance rate. Each mode is analysed with the Routh–Hurwitz criterion: the first and third Hurwitz determinants stay positive in $\mathcal{I}$, while the second is negative only on a set $\mathcal{P}_k$. These sets are nested, $\mathcal{P}_{K_2} \subseteq \cdots \subseteq \mathcal{P}_1 \subseteq \mathcal{P}_0 = \mathcal{P}$, and empty for large $k$, so the zero mode is the first to destabilize. At the uninfected state, the mode equation $d_V\Delta V = c(\lambda)V$ with $c(\lambda) = \lambda + \mu_V - \gamma\mu_I N T_u/(\lambda + \mu_I)$ has a positive root exactly when $R_0 > 1$.

## Sources

- C.-M. Brauner, X. Fan and L. Lorenzi, "Two-dimensional stability analysis in a HIV model with quadratic logistic growth term", arXiv:1211.0136 (2012): model in Section 1; Theorem 2.1 (equilibria, Section 2); Theorems 3.1 and 3.2 (stability of the uninfected and infected equilibria) and Propositions 3.3, 3.5, 3.7 (mode analysis, Section 3). <https://doi.org/10.48550/arXiv.1211.0136>. Published version: Communications on Pure and Applied Analysis 12(5) (2013), 1813–1844, <https://doi.org/10.3934/cpaa.2013.12.1813>; locators above refer to the arXiv version.

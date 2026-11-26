# Well-posedness of a degenerate two-region reaction-diffusion SIR model with switching mobility

**Model.** A domain $\Omega \subset \mathbb{R}^d$ is split by an interface $\Gamma$ into two regions $\Omega_1, \Omega_2$. In region $i$ (with $j \ne i$ the other region) let $u^i = (S^i, I^i, R^i)$. With recruitment $\Lambda_i N_i$, within- and cross-region transmission $\beta_i, \beta_{ij}$, recovery $\gamma_i$ and mortalities $\mu_S, \mu_I, \mu_R$, the reaction term is

$$
f(u^i, u^j) = \begin{pmatrix} \Lambda_i N_i - \mu_S S^i - (\beta_i I^i + \beta_{ij} I^j) S^i \\ (\beta_i I^i + \beta_{ij} I^j) S^i - (\gamma_i + \mu_I) I^i \\ \gamma_i I^i - \mu_R R^i \end{pmatrix}.
$$

Each class $k \in \{S, I, R\}$ leaves region $i$ with probability $\lambda_{k,i}$, and diffuses with coefficient $\sigma_i(\lambda_{k,i})$, collected in $A_i = \operatorname{diag}(\sigma_{S,i}, \sigma_{I,i}, \sigma_{R,i})$, which may vanish where the population density vanishes (degenerate diffusion). Writing $\lambda_i = (\lambda_{S,i}, \lambda_{I,i}, \lambda_{R,i})$, the system is

$$
\begin{aligned}
\partial_t u^i - \operatorname{div}(A_i \nabla u^i) &= f(u^i, u^j) + \operatorname{div}(A_j \nabla u^j) + \lambda_j u^j - \lambda_i u^i && \text{in } (0,T)\times\Omega_i,\\
A_i \nabla u^i\cdot\tau + A_j \nabla u^j\cdot\tau + \alpha^j(I^i)\, u^j &= 0 && \text{on } (0,T)\times\Gamma,\\
u^i &= 0 && \text{on } (0,T)\times\partial\Omega_i \setminus \Gamma ,
\end{aligned}
$$

with non-negative initial data $u^i_0 \in L^2$. The interface mobility is $\alpha^j_k(I) = \alpha(I)$ if $I \ge I^j_{\mathrm{th}}$ and $-\alpha(I)$ otherwise, for a Lipschitz function $\alpha \ge 0$ with $\alpha(I) \to 0$ as $I \to \infty$. Crossing the infection threshold reverses the direction of migration, and $\alpha \equiv 0$ (lockdown) turns the Robin interface condition into a Neumann one.

**Weak degeneracy.** The coefficients $\sigma_i$ are positive except on a negligible set, with $\partial_t\sigma_i/\sigma_i \in L^\infty$ and $1/\sigma_i$ locally integrable in space-time near every point. Solutions are sought in the weighted spaces $H^1_{A_i}(\Omega) = \{u \in L^2 : \nabla u\cdot A_i \nabla u \in L^1\}$, and $H^1_{A_i,0}(\Omega)$ embeds compactly in $L^2(\Omega)$.

**Theorem (well-posedness).** For every $T > 0$ and non-negative $u^i_0 \in L^2(\Omega)$, $i = 1, 2$, the problem has a unique non-negative weak solution

$$
(u^1, u^2) \in L^\infty(0,T; L^2(\Omega))^2 \cap L^2(0,T; H^1_{A_1,0}) \times L^2(0,T; H^1_{A_2,0}), \qquad (\partial_t u^1, \partial_t u^2) \in L^2(0,T; H^{-1}_{A_1,0}) \times L^2(0,T; H^{-1}_{A_2,0}).
$$

## Expansion

The proof uses Faedo-Galerkin approximation in the weighted spaces. Energy estimates follow by testing with $u^i$; the cross-diffusion and interface terms are controlled with the weighted Poincaré inequality, the trace inequality in $H^1_{A_i}$ and the boundedness of $\alpha$. Compactness comes from the compact embedding of $H^1_{A_i,0}$ in $L^2$ together with the time-derivative bound (Aubin-Lions), which allows passage to the limit in the bilinear incidence terms. Non-negativity follows by testing with negative parts, since every reaction term that can decrease a component is proportional to that component. Uniqueness follows from a Gronwall estimate for the difference of two solutions, using the Lipschitz continuity of $\alpha$ and of the incidence on bounded sets. The degenerate diffusion slows spatial spread near borders where density vanishes, and the switching interface condition models policy-driven reversal or shutdown of migration.

## Sources

- Omar Elamraoui, Jawad Salhi and Abderrahim Zafrar, "A degenerate reaction-diffusion SIR model in interconnected regions", arXiv (2026), Section 2 (model, interface conditions, weak degeneracy assumptions), Section 3 (Proposition 1, Definition 1, Theorem 1 and Proposition 2), <https://doi.org/10.48550/arXiv.2605.11925>.

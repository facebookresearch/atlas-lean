# Disease-free stability of the two-patch reinfection model

For patches $j\in\{u,r\}$ (urban, rural) let $S_j$, $I_j$, $\widetilde S_j$ be susceptible, infected and post-recovery susceptible numbers, $N_j=S_j+I_j+\widetilde S_j$, with equal birth and death rate $\mu_j$, infection rate $\beta_j$, recovery rate $\gamma_j$, reinfection rate $\rho_j$, and constant movement fractions $\delta_{ur}$ (urban to rural) and $\delta_{ru}$ (rural to urban). The urban equations are

$$\begin{aligned}\dot S_u&=\mu_uN_u-\beta_u\frac{I_u}{N_u}S_u-\mu_uS_u+\delta_{ru}S_r-\delta_{ur}S_u,\\ \dot I_u&=\beta_u\frac{I_u}{N_u}S_u-(\mu_u+\gamma_u)I_u+\rho_u\frac{I_u}{N_u}\widetilde S_u+\delta_{ru}I_r-\delta_{ur}I_u,\\ \dot{\widetilde S}_u&=\gamma_uI_u-\rho_u\frac{I_u}{N_u}\widetilde S_u-\mu_u\widetilde S_u+\delta_{ru}\widetilde S_r-\delta_{ur}\widetilde S_u,\end{aligned}$$

and the rural equations are obtained by swapping $u\leftrightarrow r$. Total patch sizes obey the linear system $\dot N_u=-\delta_{ur}N_u+\delta_{ru}N_r=-\dot N_r$. The local basic reproduction numbers are

$$\mathcal R_{0u}=\frac{\beta_u}{\gamma_u+\mu_u},\qquad \mathcal R_{0r}=\frac{\beta_r}{\gamma_r+\mu_r}.$$

**Theorem.** Suppose

$$\mathcal R_{0u}<1+\frac{\delta_{ur}}{\mu_u+\gamma_u},\qquad \mathcal R_{0r}<1+\frac{\delta_{ru}}{\mu_r+\gamma_r},$$

$$\frac{\delta_{ur}}{\mu_u+\gamma_u}\cdot\frac{\delta_{ru}}{\mu_r+\gamma_r}<\Big(\mathcal R_{0u}-1-\frac{\delta_{ur}}{\mu_u+\gamma_u}\Big)\Big(\mathcal R_{0r}-1-\frac{\delta_{ru}}{\mu_r+\gamma_r}\Big).$$

Then the disease-free steady state $(S_u^*,0,0,S_r^*,0,0)$ is locally asymptotically stable. These conditions hold whenever $\mathcal R_{0u}<1$ and $\mathcal R_{0r}<1$, but they also allow stability when one local reproduction number exceeds $1$: movement can eliminate a disease that would persist in an isolated patch.

## Expansion

After eliminating $\widetilde S_r$ via conservation of the total population, the Jacobian at the disease-free state has five real eigenvalues: $\lambda_1=-(\delta_{ru}+\delta_{ur})$; a pair $\lambda_{2\pm}$ that is always negative; and

$$\lambda_{3\pm}=\tfrac12\Big[\eta_{ur}+\eta_{ru}\pm\sqrt{(\eta_{ur}-\eta_{ru})^2+4\delta_{ru}\delta_{ur}}\Big],\qquad \eta_{ur}=\beta_u-\delta_{ur}-\gamma_u-\mu_u,\ \ \eta_{ru}=\beta_r-\delta_{ru}-\gamma_r-\mu_r.$$

Both $\lambda_{3\pm}<0$ iff $\eta_{ur}+\eta_{ru}<0$ and $\delta_{ru}\delta_{ur}<\eta_{ur}\eta_{ru}$. Dividing by $(\mu_u+\gamma_u)(\mu_r+\gamma_r)$ gives the stated conditions: the product inequality forces $\eta_{ur},\eta_{ru}$ to share a sign, and the sum condition makes both negative. Without movement the region is the unit square $\mathcal R_{0u},\mathcal R_{0r}<1$; movement enlarges it.

## Proof depends on

- [Hurwitz criterion for $2 \times 2$ real matrices](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/hurwitz-criterion-for-two-by-two-matrices.md)
- [Lyapunov's indirect method (linearized stability), conditional decay form](../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/global-solution-decay-of-has-fderiv-at.md)

## Sources

- J. G. Calvo, A. Hernández, M. A. Porter and F. Sanchez, *A two-patch epidemic model with nonlinear reinfection*, arXiv:1907.08887 (2019), Section 2 and Lemma 3.1 (Section 3.1). <https://doi.org/10.48550/arXiv.1907.08887>

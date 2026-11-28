# Backward bifurcation in the vector-bias bed-net malaria model

**Model.** Susceptible and infectious humans $S_h, I_h$ and susceptible and infectious mosquitoes $S_v, I_v$ satisfy

$$ \dot S_h = \Lambda_h - \lambda_h S_h - \mu S_h + \delta I_h, \quad \dot I_h = \lambda_h S_h - (\alpha+\mu+\delta) I_h, \quad \dot S_v = \Lambda_v - \lambda_v S_v - \eta S_v, \quad \dot I_v = \lambda_v S_v - \eta I_v, $$

with all parameters positive, forces of infection

$$ \lambda_h = \frac{p_1 \beta\, I_v}{\pi I_h + S_h}, \qquad \lambda_v = \frac{\pi p_2 \beta\, I_h}{\pi I_h + S_h}, $$

vector-bias parameter $\pi = p/q \ge 1$ (ratio of the probabilities that a mosquito bites an infectious versus a susceptible human), and bed-net usage $b \in [0,1]$ entering through $\eta = \eta_{\mathrm{nat}} + \eta_{\mathrm{bn}} b$ and $\beta = \beta_{\max} - b(\beta_{\max} - \beta_{\min})$. Write $\alpha_0 = \alpha + \mu + \delta$. The disease-free equilibrium is $E_0 = (\Lambda_h/\mu, 0, \Lambda_v/\eta, 0)$ and

$$ R_0 = \frac{\pi p_1 p_2 \mu \Lambda_v \beta^2}{\Lambda_h \eta^2 \alpha_0}. $$

**Theorem.**

1. $E_0$ is locally asymptotically stable if $R_0 < 1$ and unstable if $R_0 > 1$.
2. Endemic equilibria correspond to positive roots $\lambda_h^*$ of $A_0 (\lambda_h^*)^2 + B_0 \lambda_h^* + C_0 = 0$ with $A_0 = \eta \Lambda_h \pi^2 (\eta + p_2\beta) > 0$, $B_0 = \pi\big[\eta \alpha_0 \Lambda_h (2\eta + p_2\beta) - p_1 p_2 \beta^2 \Lambda_v (\alpha + \mu)\big]$ and $C_0 = \eta^2 \alpha_0^2 \Lambda_h (1 - R_0)$. Hence there is a unique endemic equilibrium when $R_0 > 1$, and two endemic equilibria when $C_0 > 0$, $B_0 < 0$ and $B_0^2 - 4A_0C_0 > 0$, which is possible with $R_0 < 1$.
3. Let

$$ \Theta = \frac{\alpha + \mu}{\Lambda_h} - \frac{2\pi\mu}{\Lambda_h} - \frac{\alpha_0 \eta}{\beta p_1 \Lambda_v}. $$

   If $\Theta > 0$ the system undergoes a backward bifurcation at $R_0 = 1$ (an unstable endemic branch exists for $R_0$ slightly below $1$); if $\Theta < 0$ the bifurcation is forward.
4. If the mosquito population is at its equilibrium $N_v \equiv \Lambda_v/\eta$ and $R_0 > 1$, the unique endemic equilibrium is globally asymptotically stable in the interior of the feasible region.

## Expansion

At $E_0$ the Jacobian has eigenvalues $-\mu$, $-\eta$ and those of the $2\times2$ block $\begin{pmatrix} -\alpha_0 & p_1\beta \\ \varphi & -\eta\end{pmatrix}$ with $\varphi = \pi p_2 \beta \mu \Lambda_v/(\eta \Lambda_h)$; its trace is negative and its determinant equals $\alpha_0 \eta (1 - R_0)$. Solving the equilibrium equations for the human and mosquito compartments in terms of $\lambda_h^*$ and $\lambda_v^* = \pi p_2 \beta \lambda_h^*/(\pi \lambda_h^* + \alpha_0)$ reduces existence to the displayed quadratic, and Descartes' rule of signs gives the count. Taking $p_2$ as bifurcation parameter, the Castillo-Chavez–Song centre manifold theorem gives the normal form $\dot u = a u^2 + \kappa\,\xi u$ with $\kappa > 0$, and an explicit computation yields $a = \frac{2 p_1 \beta \eta}{\eta + \alpha_0}\,\Theta$. Since $\pi \ge 1$, $\alpha = 0$ forces $\Theta < 0$: disease-induced mortality is what makes the backward case possible, while $\pi$ and $b$ move $\Theta$ through the terms $-2\pi\mu/\Lambda_h$ and $-\alpha_0\eta/(\beta p_1 \Lambda_v)$. Global stability uses the Li–Muldowney geometric approach on the reduced three-dimensional system: uniform persistence (from instability of $E_0$) gives an absorbing compact set, and a Bendixson criterion with a Lozinskiĭ measure of the second additive compound matrix excludes periodic orbits.

## Sources

- Bruno Buonomo, "Analysis of a malaria model with mosquito host choice and bed-net control", arXiv:1311.3209 (2013), Section 2 (system (1), forces of infection (2), $R_0$ (6), Theorems 2.1–2.2), Section 3 (centre manifold coefficients, Theorem 3.1), Section 4 (Theorem 4.1), Appendix (Theorem A.1). <https://doi.org/10.48550/arXiv.1311.3209>. Published version: International Journal of Biomathematics 08(06) (2015), article 1550077, <https://doi.org/10.1142/s1793524515500771>; locators above refer to the arXiv version.

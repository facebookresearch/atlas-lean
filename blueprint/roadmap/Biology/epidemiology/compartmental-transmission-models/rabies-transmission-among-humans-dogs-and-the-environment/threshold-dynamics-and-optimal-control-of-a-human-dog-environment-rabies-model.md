# Threshold dynamics and optimal control of a human–dog–environment rabies model

**Model.** Humans ($S_H, E_H, I_H, R_H$), free-range dogs ($S_F, E_F, I_F$), domestic dogs ($S_D, E_D, I_D, R_D$) and the environmental virus concentration $M$ interact through the saturating environmental force $\lambda(M) = M/(M + C)$. With recruitment rates $\theta_i$, natural death rates $\mu_i$, disease death rates $\sigma_i$ and controls $u_1$ (health promotion), $u_2$ (domestic-dog vaccination), $u_3$ (human protective behavior) and $u_4$ (post-exposure treatment of exposed humans and dogs), the human equations are

$$\dot S_H = \theta_1 + \beta_3 R_H - \mu_1 S_H - (1 - u_1 - u_3)\big(\tau_1 I_F + \tau_2 I_D + \tau_3\lambda(M)\big)S_H,$$

$$\dot E_H = (1 - u_1 - u_3)\big(\tau_1 I_F + \tau_2 I_D + \tau_3\lambda(M)\big)S_H - (\mu_1 + \beta_1 + \beta_2 + u_4)E_H, \quad \dot I_H = \beta_1 E_H - (\sigma_1 + \mu_1)I_H, \quad \dot R_H = (\beta_2 + u_4)E_H - (\beta_3 + \mu_1)R_H;$$

the free-range dogs (uncontrolled) satisfy

$$\dot S_F = \theta_2 - \big(\kappa_1 I_F + \kappa_2 I_D + \kappa_3\lambda(M)\big)S_F - \mu_2 S_F, \quad \dot E_F = \big(\kappa_1 I_F + \kappa_2 I_D + \kappa_3\lambda(M)\big)S_F - (\mu_2 + \gamma)E_F, \quad \dot I_F = \gamma E_F - (\mu_2 + \sigma_2)I_F;$$

with the domestic-dog force $\Phi_D = (1 - u_1 - u_2)\big(\frac{\psi_1 I_F}{1+\rho_1} + \frac{\psi_2 I_D}{1+\rho_2} + \frac{\psi_3\lambda(M)}{1+\rho_3}\big)$, where the $\rho_i$ are deterrence factors, the domestic dogs satisfy

$$\dot S_D = \theta_3 - \mu_3 S_D - \Phi_D S_D + \gamma_3 R_D, \quad \dot E_D = \Phi_D S_D - (\mu_3 + \gamma_1 + \gamma_2 + u_4)E_D, \quad \dot I_D = \gamma_1 E_D - (\mu_3 + \sigma_3)I_D, \quad \dot R_D = (\gamma_2 + u_4)E_D - (\mu_3 + \gamma_3)R_D;$$

and the environment obeys $\dot M = \nu_1 I_H + \nu_2 I_F + \nu_3 I_D - \mu_4 M$ (the source's system (1)). The effective reproduction number is the source's (16),

$$\mathcal{R}_e = \frac{R_{33} + R_{21} + \sqrt{R_{21}^2 - 2R_{33}R_{21} + 4R_{31}R_{23} + R_{33}^2}}{2},$$

with $R_{21} = \frac{\kappa_1\theta_2\gamma}{\mu_2(\mu_2+\gamma)(\sigma_2+\mu_2)}$, $R_{23} = \frac{\kappa_2\theta_2 a_3}{\mu_2}$, $R_{31} = \frac{(1-u_1-u_2)\psi_1\theta_3\gamma}{(1+\rho_1)\mu_3(\mu_2+\gamma)(\sigma_2+\mu_2)}$, $R_{33} = \frac{(1-u_1-u_2)\psi_2\theta_3 a_3}{(1+\rho_2)\mu_3}$ and $a_3 = \frac{\gamma}{(\mu_3+\gamma_1+\gamma_2+u_4)(\sigma_3+\mu_3)}$, as printed; $\mathcal{R}_0$ is its value without controls. (The source obtains it as the spectral radius of $FV^{-1}$ for its (14)–(15), whose $F$ has a zero column for $M$; the spectral radius of the full next-generation matrix with the environmental route can differ.)

**Theorem.**

1. *(Well-posedness.)* Solutions starting in the nonnegative orthant remain positive and are uniformly bounded.
2. *(Disease-free equilibrium.)* The rabies-free equilibrium is globally asymptotically stable when $\mathcal{R}_0 < 1$ and unstable otherwise (the source's Theorem 3).
3. *(Endemic equilibrium.)* If $\mathcal{R}_e \ge 1$, the system has exactly one equilibrium with $E_H, E_F, E_D > 0$ (the source's Theorem 4, whose hypothesis "$E_H, E_F, E_D > 0$" is a condition on the equilibrium sought), and it is globally asymptotically stable when $\mathcal{R}_e > 1$.
4. *(Optimal control.)* For the objective (the source's (22))

$$J(u_1,\dots,u_4) = \int_{t_0}^{t_f}\Big(K_1M + K_2E_H + K_3I_H + K_4E_D + K_5I_D - K_6S_D + \frac12\sum_{j=1}^4A_ju_j^2\Big)dt,$$

with positive weights $K_i$, $A_j$ (the term $-K_6S_D$ rewards susceptible domestic dogs), minimized over bounded measurable controls with values in $[0,1]$, an optimal control exists and is unique, and it satisfies Pontryagin's principle: there are adjoint variables $\lambda_1, \dots, \lambda_{12}$ with $\lambda_j' = -\partial H/\partial y_j$ and $\lambda_j(t_f) = 0$, and each optimal control is the projection onto its admissible interval of the stationary point of the Hamiltonian, e.g. $u_1^* = \max\{0, \min(1, \cdot)\}$ with an explicit expression in the adjoint differences $\lambda_2 - \lambda_1$, $\lambda_9 - \lambda_8$ and the forces of infection.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Positivity follows from integrating each equation with an integrating factor, and boundedness from the linear inequalities satisfied by the host totals ($\dot N_H \le \theta_1 - \mu_1 N_H$ and analogues) and then by $M$. Global stability of the rabies-free state uses the Castillo-Chavez decomposition into non-transmitting and transmitting compartments, $\dot U_s = G_1(U_s - U_s^0) + G_{12}U_i$, $\dot U_i = G_2 U_i$, with $G_2$ Metzler and the non-transmitting block having only negative eigenvalues; global stability of the endemic state uses a Volterra-type function $\sum c_i (x_i - x_i^* - x_i^*\ln(x_i/x_i^*))$ together with the inequality $1 - y + \ln y \le 0$ for $y > 0$. Existence of an optimal control follows from convexity of the integrand in the controls, compactness of the control set and the a priori bounds; uniqueness is argued by comparing two optimal controls through the Lipschitz dependence of the state–adjoint system on the controls. Sensitivity analysis shows $\mathcal{R}_e$ decreasing in vaccination, health promotion and treatment and increasing in dog-to-dog contact.

## Sources

- Mfano Charles, Sayoki G. Mfinanga, G. A. Lyakurwa, Delfim F. M. Torres, Verdiana G. Masanja, "A Mathematical and Optimal Control Model for Rabies Transmission Dynamics Among Humans and Dogs With Environmental Effects", Journal of Applied Mathematics 2025 (2025), 5559842, <https://doi.org/10.1155/jama/5559842>. Published version of arXiv:2507.08895, cited next; locators there refer to the arXiv version.
- Mfano Charles, Sayoki G. Mfinanga, G. A. Lyakurwa, Delfim F. M. Torres, "A Mathematical and Optimal Control Model for Rabies Transmission Dynamics Among Humans and Dogs with Environmental Effects", arXiv (2025). Section 2 (model), Lemma 1, Theorems 2–7, appendix theorem on the endemic equilibrium. <https://doi.org/10.48550/arXiv.2507.08895>

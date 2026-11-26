# Reproduction number and optimal control of the HIV/AIDS model with unaware infectives

Let $S$ be susceptibles, $I_1$ HIV-positive individuals unaware of their infection, $I_2$ aware HIV-positive individuals, $A$ individuals with AIDS, and $N = S + I_1 + I_2 + A$. With recruitment $Q_0$, natural mortality $\mu$, awareness (screening) rate $\theta$, progression rates $\delta$ and $\pi$, AIDS mortality $\alpha$, transmission probabilities $\beta_k$ and contact rates $c_k$, and condom-use effort $u_1 \in [0,1]$,

$$

\beta_m = \frac{(1-u_1)\,(\beta_1c_1 I_1 + \beta_2 c_2 I_2 + \beta_3 c_3 A)}{N},

$$

$$

\begin{aligned}
S' &= Q_0 - \beta_m S - \mu S, & I_1' &= \beta_m S - (\theta+\mu+\delta)I_1,\\
I_2' &= \theta I_1 - (\delta+\mu+\pi)I_2, & A' &= \delta I_1 + (\delta+\pi)I_2 - (\alpha+\mu)A .
\end{aligned}

$$

**Theorem (threshold).** Solutions with nonnegative data stay nonnegative, and the region $\{N \le Q_0/\mu\}$ is positively invariant and attracting. The disease-free equilibrium is $E_0 = (Q_0/\mu,0,0,0)$, and the next-generation matrix gives $\mathcal R_0 = \zeta_1 + \zeta_2 + \zeta_3 + \zeta_4$ with

$$

\zeta_1 = \frac{(1-u_1)\beta_1c_1}{\theta+\delta+\mu}, \quad
\zeta_2 = \frac{(1-u_1)\beta_2c_2\,\theta}{(\theta+\delta+\mu)(\delta+\mu+\pi)}, \quad
\zeta_3 = \frac{(1-u_1)\beta_3c_3\,\theta(\delta+\pi)}{(\theta+\delta+\mu)(\delta+\mu+\pi)(\alpha+\mu)}, \quad
\zeta_4 = \frac{(1-u_1)\beta_3c_3\,\delta}{(\theta+\delta+\mu)(\alpha+\mu)},

$$

the contributions of transmission by unaware infectives, aware infectives, and AIDS patients reached through the aware and unaware routes. If $\mathcal R_0 < 1$, $E_0$ is the only equilibrium and is asymptotically stable; if $\mathcal R_0 > 1$, $E_0$ is unstable and there is a locally asymptotically stable endemic equilibrium $E_1$.

**Theorem (optimal control).** Let the screening and treatment efforts $u_2, u_3 \in [0,1]$ replace $\theta$ by $u_2\theta$ and $\pi$ by $u_3\pi$, and minimize

$$

J(u_1,u_2,u_3) = \int_0^T \big(a I_1 + b_1u_1^2 + b_2u_2^2 + b_3u_3^2\big)\,dt

$$

over measurable controls with values in $[0,1]$. An optimal control exists, and with adjoint variables $\lambda_S, \lambda_{I_1}, \lambda_{I_2}, \lambda_A$ solving the Pontryagin adjoint system with zero terminal values,

$$

u_1^* = \max\Big\{0,\min\Big(1,\frac{(\beta_1c_1I_1 + \beta_2c_2I_2 + \beta_3c_3A)\,S}{2b_1N}(\lambda_{I_1} - \lambda_S)\Big)\Big\},

$$

$$

u_2^* = \max\Big\{0,\min\Big(1,\frac{\theta I_1(\lambda_{I_1} - \lambda_{I_2})}{2b_2}\Big)\Big\}, \qquad
u_3^* = \max\Big\{0,\min\Big(1,\frac{\pi I_2(\lambda_{I_2} - \lambda_A)}{2b_3}\Big)\Big\}.

$$

## Expansion

The infected subsystem $(I_1,I_2,A)$ has new-infection matrix $F$ with first row $(1-u_1)(\beta_1c_1, \beta_2c_2, \beta_3c_3)$ at $E_0$ (where $S/N = 1$) and lower-triangular transition matrix $V$; since $F$ has rank one, $\rho(FV^{-1})$ is the first row of $F$ times the first column of $V^{-1}$, which yields the four terms. Existence of an optimal control follows from convexity of the integrand in the controls, compactness of the control set and boundedness of the state (Fleming–Rishel). The characterization comes from minimizing the Hamiltonian pointwise in each control, which is quadratic, and projecting onto $[0,1]$.

## Sources

- Nouar Chorfi, Salem Abdelmalek, Samir Bendoukha, "Stability analysis and optimal control of an HIV/AIDS epidemic model", arXiv (2023). Sections 2–3 (Theorems 1–2), Section 3 ($\mathcal R_0$, Theorem 3), Section 4 (Theorems 4–5), Section 5 (existence of the optimal control and Theorem 6). <https://doi.org/10.48550/arXiv.2304.08251>

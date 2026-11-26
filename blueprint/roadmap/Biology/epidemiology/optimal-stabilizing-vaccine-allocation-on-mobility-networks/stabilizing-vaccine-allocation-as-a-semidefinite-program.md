# Optimal stabilizing vaccine allocation as a semidefinite program

**Model.** In a network of $n$ locations with populations $N_i^*$, let $s_i$, $x_i^{\mathrm a}$, $x_i^{\mathrm s}$ be the susceptible, asymptomatic-infected and symptomatic-infected fractions at location $i$:

$$\begin{aligned} \dot s_i&=-s_i\sum_ja_{ij}\big(\beta^{\mathrm a}x_j^{\mathrm a}+\beta^{\mathrm s}x_j^{\mathrm s}\big),\\ \dot x_i^{\mathrm a}&=s_i\sum_ja_{ij}\big(\beta^{\mathrm a}x_j^{\mathrm a}+\beta^{\mathrm s}x_j^{\mathrm s}\big)-(\epsilon+r^{\mathrm a})x_i^{\mathrm a},\\ \dot x_i^{\mathrm s}&=\epsilon x_i^{\mathrm a}-\rho_{\mathrm s}x_i^{\mathrm s}, \end{aligned}$$

where $\rho_{\mathrm s}$ is the total exit rate (recovery plus death) of symptomatic cases. Mixing comes from a mobility matrix $\tau=(\tau_{ij})$ (fraction of residents of $i$ visiting $j$): $A=(a_{ij})=\bar A\,\mathrm{diag}(N_i^*)$ with

$$\bar A=\tau\,\mathrm{diag}\Big(\sum_kN_k^*\tau_{kl}\Big)^{-1}\tau^\top,$$

a symmetric positive definite matrix when $\tau$ has full rank. The infected block of the Jacobian at susceptibility profile $s$ is $M(s)=\begin{pmatrix}\beta^{\mathrm a}\mathrm{diag}(s)A-(\epsilon+r^{\mathrm a})&\beta^{\mathrm s}\mathrm{diag}(s)A\\ \epsilon&-\rho_{\mathrm s}\end{pmatrix}$, and $\lambda_{\max}(M(s(t_0)))\le-\alpha$ guarantees that a positive combination of the infected fractions decays to zero at rate at least $\alpha$ from time $t_0$ on, whatever happens later (since $s$ only decreases).

**Problem.** Vaccinating a fraction $v_i$ of location $i$ at $t_0$ with efficacy $\psi$ replaces $s_i(t_0)$ by $s_i(t_0)-\psi v_i$. The optimal stabilizing allocation for decay rate $\alpha$ is

$$\min_v\ \sum_iN_i^*v_i\quad\text{s.t.}\quad\lambda_{\max}\big(M(s(t_0)-\psi v)\big)\le-\alpha,\qquad0\le v_i\le s_i(t_0).$$

**Theorem (SDP reformulation).** Let $0<\alpha<\min(\epsilon+r^{\mathrm a},\rho_{\mathrm s})$ and

$$b_1=\frac{\beta^{\mathrm s}\epsilon+\beta^{\mathrm a}(\rho_{\mathrm s}-\alpha)}{(\epsilon+r^{\mathrm a}-\alpha)(\rho_{\mathrm s}-\alpha)} .$$

With the change of variables $u_i=N_i^*b_1\big(s_i(t_0)-\psi v_i\big)$, the problem is equivalent to the semidefinite program

$$\min_u\ -\sum_iu_i\quad\text{s.t.}\quad\mathrm{diag}(u)\preceq\bar A^{-1},\qquad(1-\psi)s_i(t_0)N_i^*b_1\le u_i\le s_i(t_0)N_i^*b_1 .$$

The dual problem (fewest doses achieving the fastest decay for a fixed supply) is solved by bisection on $\alpha$ over this SDP.

## Expansion

Eliminating $x^{\mathrm s}$ from the eigenvalue equation at $\lambda=-\alpha$ shows that $\lambda_{\max}(M)\le-\alpha$ holds exactly when $b_1\,\mathrm{diag}(s)A$ is discrete-time stable (spectral radius at most one). Since nonzero eigenvalues of $XY$ and $YX$ coincide, this is stability of $\mathrm{diag}(N_i^*b_1s_i)\bar A$, which for a positive diagonal matrix and a positive definite $\bar A$ is equivalent to $\bar A\preceq\mathrm{diag}\big(1/(N_i^*b_1s_i)\big)$. Inverting both positive definite sides gives the linear matrix inequality $\mathrm{diag}(N_i^*b_1s_i)\preceq\bar A^{-1}$, linear in the post-vaccination susceptibility, hence in $v$. The allocation is a single fixed policy rather than a time-varying control, and its certificate remains valid as susceptibility depletes. With age structure, $\bar A$ is replaced by $\bar A\otimes\Gamma$ for an intrinsic contact matrix $\Gamma$; the SDP form survives only when this Kronecker product is positive definite.

## Sources

- Qianqian Ma, Yang-Yu Liu, Alex Olshevsky, "Optimal Vaccine Allocation for Pandemic Stabilization", arXiv:2109.04612 (2021): model (Section 2.1) and matrix form, Section 2.3 (problem and SDP), Section 2.4 (demographic structure), Supplementary Section 6.2 (reduction to the SDP). <https://doi.org/10.48550/arXiv.2109.04612>

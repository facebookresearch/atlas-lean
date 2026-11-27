# Incommensurate fractional stability and the threshold of the fractional SEIQRP model

**Fractional calculus.** For $0 < \alpha < 1$ the Caputo derivative is ${}^C D^\alpha_{t_0,t}f(t) = \frac{1}{\Gamma(1-\alpha)}\int_{t_0}^t (t-s)^{-\alpha}f'(s)\,ds$. A system ${}^C D^{\alpha}x = f(t,x)$ with order vector $\alpha = (\alpha_1,\dots,\alpha_n)$ is *commensurate* if all $\alpha_i$ are equal and *incommensurate* otherwise; if $f$ is continuous and Lipschitz in $x$ it has a unique solution.

**Stability criterion (incommensurate linear systems).** Consider ${}^C D^\alpha_{0,t}x = Ax$ with $A \in \mathbb{R}^{n\times n}$ and rational orders $\alpha_i = n_i/d_i \in (0,1]$ in lowest terms, and let $M$ be the least common multiple of the $d_i$. If every root $\lambda$ of

$$\det\big(\operatorname{diag}(\lambda^{M\alpha_1},\dots,\lambda^{M\alpha_n}) - A\big) = 0$$

satisfies $|\arg\lambda| > \pi/(2M)$, then the zero solution is globally asymptotically stable. In the commensurate case $\alpha_i = \alpha$ this reduces to Matignon's condition $|\arg\lambda_i(A)| > \alpha\pi/2$ on the eigenvalues of $A$. Nonlinear systems are treated through the Jacobian at an equilibrium.

**Model.** The generalized SEIR model with protection and quarantine,

$$\begin{aligned}
\dot S &= \Lambda - \beta_1 SE - \beta_2 SI - (\mu+\rho)S, & \dot E &= \beta_1 SE + \beta_2 SI - (\gamma+\rho)E, & \dot I &= \gamma E - (\delta+\rho)I,\\
\dot Q &= \delta I - (\theta+\rho+\eta)Q, & \dot R &= \theta Q - \rho R, & \dot P &= \mu S - \rho P,
\end{aligned}$$

($\Lambda$ inflow, $\beta_1,\beta_2$ transmission by exposed and infectious individuals, $\mu$ protection, $\rho$ natural death, $\gamma^{-1}$ latency, $\delta$ quarantine, $\theta$ recovery, $\eta$ disease death) has basic reproduction number

$$R_0 = \frac{\Lambda\big(\beta_1(\delta+\rho) + \beta_2\gamma\big)}{(\gamma+\rho)(\delta+\rho)(\mu+\rho)} .$$

Its two-sided fractional version replaces the derivatives by Caputo derivatives with compartment-dependent orders. Solutions from nonnegative data are unique, nonnegative and remain in $\{S+E+I+Q+R+P \le \Lambda/\rho\}$. In the commensurate case the disease-free equilibrium $P_F = (\Lambda/(\mu+\rho),0,0,0,0,\mu\Lambda/(\rho(\mu+\rho)))$ is locally asymptotically stable if $R_0 < 1$ and unstable if $R_0 > 1$; an endemic equilibrium exists iff $R_0 > 1$, and in the incommensurate cases stability of each equilibrium holds whenever the roots of the corresponding factors of the characteristic equation satisfy $|\arg\lambda| > \pi/(2M)$.

## Depends on

- [Basic reproduction number from the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

At $P_F$ the infected subsystem $(E,I)$ has new-infection matrix $F = \begin{pmatrix}\beta_1 S^* & \beta_2 S^*\\ 0 & 0\end{pmatrix}$ and transition matrix $V = \begin{pmatrix}\gamma+\rho & 0\\ -\gamma & \delta+\rho\end{pmatrix}$ with $S^* = \Lambda/(\mu+\rho)$, and $R_0 = \rho(FV^{-1}) = \frac{\beta_1S^*}{\gamma+\rho} + \frac{\beta_2\gamma S^*}{(\gamma+\rho)(\delta+\rho)}$. The remaining Jacobian blocks are triangular with negative diagonal, so in the commensurate case all eigenvalues are real negative or have $|\arg\lambda| > \alpha\pi/2$ exactly when the $(E,I)$ block is Hurwitz, i.e. $R_0 < 1$; for $R_0 > 1$ a positive real eigenvalue violates every sector condition. The incommensurate criterion follows by substituting $s = \lambda^M$, which maps the stability sector of each fractional order to a common sector for the integer-order pseudo-polynomial.

## Sources

- W. Ma, Y. Zhao, L. Guo, Y. Chen, "Qualitative and quantitative analysis of the COVID-19 pandemic by a two-side fractional-order compartmental model", ISA Transactions (2022), Definitions 1–4, Lemmas 1–3, model (4) and its fractional forms, the expression for $R_0$, Theorems 1–7, <https://doi.org/10.1016/j.isatra.2022.01.008>, PMCID PMC8753533.

# Threshold dynamics of an SIR-like kinetic model with viral-load-dependent isolation

**Model.** Each agent carries a compartment label and a viral load $v\in[0,1]$. Susceptibles have $v=0$. A contact with an infectious agent, at frequency $\lambda_\beta$, infects with probability $\nu_\beta$ and sets $v=v_0$. Infected agents move first through a stage $I_1$ in which the viral load grows, $v\mapsto v+\nu_1(1-v)$ at rate $\lambda_\gamma$, then through a stage $I_2$ in which it decays, $v\mapsto(1-\nu_2)v$. Infectious agents are isolated (classes $H_1,H_2$) with a probability proportional to their viral load, $\alpha_H(v)=\alpha v$, at a testing frequency proportional to infectious prevalence, $\lambda_\alpha\rho_{I_j}$. There are births at rate $\lambda_bb$ and natural deaths at rate $\lambda_\mu\mu$. Taking the zeroth moments $\rho_j=\int f_j\,dv$ (densities) and first moments $n_j=\int vf_j\,dv$ (viral-load mass) of the kinetic equations gives a closed system. Its infection-relevant part is

$$\begin{aligned}
\dot\rho_S&=\lambda_bb-\lambda_\beta\nu_\beta\rho_S(\rho_{I_1}+\rho_{I_2})-\lambda_\mu\mu\rho_S,\\
\dot\rho_{I_1}&=\lambda_\beta\nu_\beta\rho_S(\rho_{I_1}+\rho_{I_2})-\lambda_\alpha\alpha\rho_{I_1}n_{I_1}-(\lambda_\gamma\nu_1+\lambda_\mu\mu)\rho_{I_1},\\
\dot\rho_{I_2}&=\lambda_\gamma\nu_1\rho_{I_1}-\lambda_\alpha\alpha\rho_{I_2}n_{I_2}-(\lambda_\gamma\nu_2+\lambda_\mu\mu)\rho_{I_2},
\end{aligned}$$

together with equations for $n_{I_1},n_{I_2}$. In those equations isolation acts quadratically, through the terms $-\lambda_\alpha\alpha n_{I_j}^2$. The region $\mathcal D$ where $\rho_S+\rho_{I_1}+\rho_{I_2}\le\lambda_bb/(\lambda_\mu\mu)$ and $n_{I_j}\le\rho_{I_j}$ is positively invariant.

**Theorem.** Let

$$\mathcal R_0=\lambda_\beta\nu_\beta\,\frac{\lambda_bb}{\lambda_\mu\mu}\,\frac{\lambda_\gamma\nu_1+\lambda_\gamma\nu_2+\lambda_\mu\mu}{(\lambda_\gamma\nu_1+\lambda_\mu\mu)(\lambda_\gamma\nu_2+\lambda_\mu\mu)} .$$

1. The unique disease-free equilibrium $\big(\frac{\lambda_bb}{\lambda_\mu\mu},0,0,0,0\big)$ is locally asymptotically stable if $\mathcal R_0<1$ and unstable if $\mathcal R_0>1$.
2. It is globally asymptotically stable in $\mathcal D$ if $\mathcal R_0<1$.
3. At $\mathcal R_0=1$ the system undergoes a forward (transcritical) bifurcation: a stable endemic branch emerges for $\mathcal R_0$ slightly above $1$, and there is no backward bifurcation. At an endemic equilibrium both $\rho_{I_1}$ and $\rho_{I_2}$ are positive.

Since isolation acts through $n_{I_j}$, which is quadratically small near the disease-free state, viral-load-dependent testing does not enter $\mathcal R_0$. It shapes the endemic level and the epidemic peak, not the invasion threshold. With constant isolation rates the model reduces to a classical SIR-type model, in which isolation enters $\mathcal R_0$ as an extra linear removal rate.

## Expansion

$\mathcal R_0$ is the transmission rate times the susceptible density at the disease-free equilibrium, times the expected total infectious time. That time is $\frac{1}{\lambda_\gamma\nu_1+\lambda_\mu\mu}$ in $I_1$, plus $\frac{\lambda_\gamma\nu_1}{\lambda_\gamma\nu_1+\lambda_\mu\mu}\cdot\frac{1}{\lambda_\gamma\nu_2+\lambda_\mu\mu}$ in $I_2$; these two terms combine into the fraction above. Global stability uses the linear Lyapunov function

$$\mathcal L=\frac{\lambda_\gamma\nu_1+\lambda_\gamma\nu_2+\lambda_\mu\mu}{\lambda_\gamma\nu_1+\lambda_\mu\mu}\,\rho_{I_1}+\rho_{I_2} .$$

Using $\rho_S\le\lambda_bb/(\lambda_\mu\mu)$ in $\mathcal D$ and dropping the nonpositive isolation terms gives $\dot{\mathcal L}\le(\lambda_\gamma\nu_2+\lambda_\mu\mu)(\mathcal R_0-1)(\rho_{I_1}+\rho_{I_2})$. The bifurcation direction follows from the Castillo-Chavez–Song centre-manifold theorem. At $\mathcal R_0=1$ the Jacobian has a simple zero eigenvalue, and the computed coefficients satisfy $A<0<B$, which gives a forward bifurcation.

These are the disease-free stability proposition, the global stability theorem and the centre-manifold theorem of Section 4 of the source.

## Proof depends on

- [LaSalle's invariance principle](../../../../Analysis/not-yet-classified/la-salle/lasalle-invariant.md)
- [Threshold theorem, stability half, conditional decay form](../../next-generation-matrix-and-the-basic-reproductio/global-solution-decay-of-r0-lt-one.md)
- [Threshold theorem, instability half, spectral form](../../next-generation-matrix-and-the-basic-reproductio/exists-re-pos-jacobian-of-one-lt-r0.md)
- [Lyapunov's indirect method, instability](../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/exists-unstable-of-has-fderiv-at.md)

## Sources

- R. Della Marca, N. Loy, A. Tosin, "An SIR-like kinetic model tracking individuals' viral load", arXiv:2106.14480 (2021). <https://doi.org/10.48550/arXiv.2106.14480>

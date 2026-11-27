# Vaccine-reduced reproduction number with prevalence-dependent attitude switching

Split each SIR class into pro-vaccination ($P$) and unprotected ($U$) subclasses. Births, at rate $\mu$, enter $S_U$; all classes die at rate $\mu$. Infection occurs at rate $\beta S_\bullet(I_P+I_U)$ and recovery at rate $\gamma$. Pro-vaccination susceptibles are vaccinated into $R_P$ at rate $\phi$, and unprotected recovereds lose immunity at rate $\theta$. Individuals switch from $P$ to $U$ at rate $\Psi(I)$ and from $U$ to $P$ at rate $\Omega(I)$, where both rates depend on the total prevalence $I=I_P+I_U$:

$$
\begin{aligned}
\dot S_P&=-\beta S_PI-(\phi+\mu+\Psi)S_P+\Omega S_U, & \dot S_U&=\mu-\beta S_UI-(\mu+\Omega)S_U+\Psi S_P+\theta R_U,\\
\dot I_\bullet&=\beta S_\bullet I-(\gamma+\mu)I_\bullet\mp(\text{attitude switching}), & \dot R_P&=\gamma I_P+\phi S_P-(\mu+\Psi)R_P+\Omega R_U,\\
&& \dot R_U&=\gamma I_U-(\theta+\mu+\Omega)R_U+\Psi R_P.
\end{aligned}
$$

At the disease-free equilibrium the susceptible fractions $S_P^0,S_U^0$ solve the linear balance of vaccination, attitude switching at $\Psi(0),\Omega(0)$, waning and demography. The disease-free equilibrium is stable if and only if the vaccine-reduced reproduction number

$$
R_v=\frac{\beta}{\gamma+\mu}\,(S_P^0+S_U^0)
$$

is less than $1$. Equivalently, stability requires the baseline pro-vaccination switching rate $\Omega(0)$ to exceed a critical value $\omega_{\rm cr}$ that is explicit in the scaled parameters. Endemic equilibria are the intersections of the prevalence-dependent switching rate with an explicit decreasing curve $\omega^*(\cdot)$ of the scaled prevalence, with $\omega^*(0)=\omega_{\rm cr}$. If attitudes respond strongly to prevalence, so that the derivatives of the switching rates at equilibrium are large, the stability inequalities for the endemic equilibrium fail. A Hopf bifurcation then produces sustained oscillations in prevalence and vaccine attitude.

## Depends on

- [Basic reproduction number from the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof sketch

Infected individuals in both attitude classes infect at the same rate and recover at the same rate, so the next-generation operator has rank one. $R_v$ is then $\beta/(\gamma+\mu)$ times the total susceptible fraction at the disease-free state. Vaccination and pro-vaccination switching lower that fraction, which is why a minimal $\Omega(0)$ is needed. The endemic-stability analysis uses a slow–fast limit ($\epsilon\to0$) in which demography is slow. In that limit the Routh–Hurwitz conditions reduce to three inequalities on $\Omega',\Psi'$ at the equilibrium.

## Sources

- Yi Jiang, Kristin M. Kurianski, Jane HyoJin Lee, Yanping Ma, Daniel Cicala and Glenn Ledder, "Incorporating changeable attitudes toward vaccination into compartment models for infectious diseases", *Mathematical Biosciences and Engineering* 22 (2025), 260–289, <https://doi.org/10.3934/mbe.2025011>. Preprint version: arXiv:2405.03931 (2024), Section 2 (model schematic and variables), Propositions 1–3, <https://doi.org/10.48550/arXiv.2405.03931>.

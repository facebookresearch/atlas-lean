# SVEIR model with saturating fomite transmission

Susceptible ($S$), exposed ($E$), infectious ($I$) and vaccinated ($V$) hosts and the environmental pathogen concentration $C$ evolve by

$$\begin{aligned}
\dot S&=\Lambda-\beta_1SI-\sigma S+(1-p)\eta V-\alpha_1S\,g(C,\kappa)-\mu S,\\
\dot E&=\beta_1SI+\beta_2IV-(\xi+\mu)E+\alpha_1S\,g(C,\kappa)+\alpha_2V\,g(C,\kappa),\\
\dot I&=\xi E-(\gamma+d+\mu)I,\\
\dot V&=\sigma S-\beta_2IV-(\eta+\mu)V-\alpha_2V\,g(C,\kappa),\\
\dot C&=\varphi I-\omega C,
\end{aligned}$$

with the Hill-type dose-response $g(C,\kappa)=C^n/(C^n+\kappa^n)$, $n\in\mathbb N$ (Holling type II for $n=1$, type III for $n\ge2$). All parameters are positive, $p\in(0,1)$, and vaccinated hosts are less susceptible: $\beta_2\le\beta_1$, $\alpha_2\le\alpha_1$. Recovered hosts ($\dot R=\gamma I-\mu R+p\eta V$) decouple.

**Invariant region.** The set

$$\Omega=\Bigl\{(S,E,I,V,C)\in\mathbb R^5_+:\ S>0,\ S+E+I+V\le\frac\Lambda\mu,\ C\le\frac{\varphi\Lambda}{\omega\mu}\Bigr\}$$

is positively invariant and globally attracting, and the system is point dissipative on $\Omega$.

**Disease-free equilibrium and reproduction numbers.** The unique disease-free equilibrium is $E_0=(S_0,0,0,V_0,0)$ with

$$S_0=\frac{\Lambda(\mu+\eta)}{\mu(\mu+\eta)+\sigma(\mu+p\eta)},\qquad V_0=\frac{\Lambda\sigma}{\mu(\mu+\eta)+\sigma(\mu+p\eta)}.$$

The control reproduction number is $\mathcal R_c=\mathcal R_c^{\rm dir}+\delta_{1n}\mathcal R_c^{\rm env}$, where

$$\mathcal R_c^{\rm dir}=\frac{\xi(\beta_1S_0+\beta_2V_0)}{(\xi+\mu)(\mu+\gamma+d)},\qquad\mathcal R_c^{\rm env}=\frac{\xi\varphi(\alpha_1S_0+\alpha_2V_0)}{\kappa\omega(\xi+\mu)(\mu+\gamma+d)},$$

and $\delta_{1n}$ is the Kronecker delta. Because $g'(0)=0$ for $n\ge2$, environmental transmission enters the invasion threshold only for the Holling type II response. Without vaccination, $\mathcal R_0=\dfrac{\xi\Lambda}{\mu(\xi+\mu)(\gamma+d+\mu)}\Bigl(\beta_1+\delta_{1n}\dfrac{\alpha_1\varphi}{\kappa\omega}\Bigr)$.

**Local stability.** If $\mathcal R_c<1$ then $E_0$ is locally asymptotically stable; if $\mathcal R_c>1$ it is unstable.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

The bounds defining $\Omega$ come from $\frac{d}{dt}(S+E+I+V)\le\Lambda-\mu(S+E+I+V)$ and $\dot C\le\varphi\Lambda/\mu-\omega C$. The reproduction number is the spectral radius of the next-generation matrix $FV^{-1}$ of the infected subsystem $(E,I,C)$ at $E_0$, in which the fomite route contributes through $g'(0)=1/\kappa$ when $n=1$ and not at all when $n\ge2$.

## Sources

- E. Penitente, U. Foryś and B. Gürbüz, "Global stability and uniform persistence in an epidemic model with saturating fomite-mediated transmission", *Ricerche di Matematica* (2026), Section 2 (model and dose-response function), Proposition 1 (proved in Appendix A), Section 3.1 (the disease-free equilibrium, $\mathcal R_c$, $\mathcal R_c^{\rm dir}$, $\mathcal R_c^{\rm env}$ and $\mathcal R_0$), Proposition 2 and Proposition 3, <https://doi.org/10.1007/s11587-026-01159-9> (preprint arXiv:2603.28285).

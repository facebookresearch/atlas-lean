# Vaccine-reduced reproduction number with prevalence-dependent attitude switching

Split each SIR class into pro-vaccination ($P$) and unprotected ($U$) subclasses. Births, at rate $\mu$, enter $S_U$; all classes die at rate $\mu$. Infection occurs at rate $\beta S_\bullet(I_P+I_U)$ and recovery at rate $\gamma$. Pro-vaccination susceptibles are vaccinated into $R_P$ at rate $\phi$, and unprotected recovereds lose immunity at rate $\theta$. Susceptible and recovered individuals switch from $P$ to $U$ at rate $\Psi(I)$ and from $U$ to $P$ at rate $\Omega(I)$, where both rates depend on the total prevalence $I=I_P+I_U$; infectious individuals keep their attitude, since they stay in that class only briefly:

$$
\begin{aligned}
\dot S_P&=-\beta S_PI-(\phi+\mu+\Psi)S_P+\Omega S_U, & \dot S_U&=\mu-\beta S_UI-(\mu+\Omega)S_U+\Psi S_P+\theta R_U,\\
\dot I_\bullet&=\beta S_\bullet I-(\gamma+\mu)I_\bullet, & \dot R_P&=\gamma I_P+\phi S_P-(\mu+\Psi)R_P+\Omega R_U,\\
&& \dot R_U&=\gamma I_U-(\theta+\mu+\Omega)R_U+\Psi R_P.
\end{aligned}
$$

At the disease-free equilibrium the susceptible fractions $S_P^0,S_U^0$ solve the linear balance of vaccination, attitude switching at $\Psi(0),\Omega(0)$, waning and demography. The disease-free equilibrium is stable if and only if the vaccine-reduced reproduction number

$$
R_v=\frac{\beta}{\gamma+\mu}\,(S_P^0+S_U^0)
$$

is less than $1$. Scale time by the lifespan and write $R_0=\beta/(\gamma+\mu)$, $\varepsilon=\mu/(\gamma+\mu)$, $v=\phi/\mu$, $h=\theta/\mu$, $\omega=\Omega/\mu$, $\psi=\Psi/\mu$, $\Sigma=\psi+\omega$, a bar for adding $1$ ($\bar h=h+1$, $\bar\Sigma=\Sigma+1$), $r=R_0-1$, $\zeta=\bar\Sigma+v$ and $\rho=\bar\Sigma(v+rh)+R_0hv$. Equivalently, the disease-free equilibrium is stable if and only if the scaled baseline switching rate exceeds a critical value,

$$
\frac{\Omega(0)}{\mu}>\omega_{\rm cr}:=\frac{r\bar h\,\bar\Sigma(0)\,\zeta(0)}{\rho(0)} .
$$

For fixed $\Sigma$, endemic equilibria are the solutions of $\omega(Y)=\omega^*(R_0Y)$, where $Y=I/\varepsilon$ is the scaled prevalence and

$$
\omega^*(y)=(\zeta+y)\,\frac{\bar\Sigma(r\bar h-y)}{\rho+R_0hy},\qquad \omega^*(0)=\omega_{\rm cr},\quad \omega^*(r\bar h)=0 ;
$$

$\omega^*$ is decreasing whenever $(1-h\zeta)R_0<\bar\Sigma\zeta+1$. If attitudes respond strongly to prevalence, so that the derivatives of the switching rates at equilibrium are large, the stability inequalities for the endemic equilibrium (in the limit $\varepsilon\to0$) fail; numerical simulations then show sustained oscillations in prevalence and vaccine attitude, but a Hopf bifurcation is not proved.

## Depends on

- [Basic reproduction number from the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof sketch

Infected individuals in both attitude classes infect at the same rate and recover at the same rate, so the next-generation operator has rank one. $R_v$ is then $\beta/(\gamma+\mu)$ times the total susceptible fraction at the disease-free state. Vaccination and pro-vaccination switching lower that fraction, which is why a minimal $\Omega(0)$ is needed. The endemic-stability analysis uses a slow–fast limit ($\epsilon\to0$) in which demography is slow. In that limit the Routh–Hurwitz conditions reduce to three inequalities on $\Omega',\Psi'$ at the equilibrium.

## Sources

- Yi Jiang, Kristin M. Kurianski, Jane HyoJin Lee, Yanping Ma, Daniel Cicala and Glenn Ledder, "Incorporating changeable attitudes toward vaccination into compartment models for infectious diseases", *Mathematical Biosciences and Engineering* 22 (2025), 260–289, <https://doi.org/10.3934/mbe.2025011>. Preprint version: arXiv:2405.03931 (2024), Section 2 (model schematic and variables), Propositions 1–3, <https://doi.org/10.48550/arXiv.2405.03931>.

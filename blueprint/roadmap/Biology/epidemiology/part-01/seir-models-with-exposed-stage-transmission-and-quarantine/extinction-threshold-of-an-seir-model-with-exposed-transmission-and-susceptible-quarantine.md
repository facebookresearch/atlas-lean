# Extinction threshold of an SEIR model with exposed-stage transmission and susceptible quarantine

**Model.** A closed population of size $N=S+E+I+E_r+R+D+Q$ is split into susceptible $S$, exposed (latent but infectious) $E$, symptomatic infected $I$, unreported recovered-from-exposed $E_r$, recovered $R$, dead $D$ and home-quarantined $Q$:

$$\begin{aligned}\dot S&=-\frac{\lambda_1}{N}SE-\frac{\lambda_2}{N}SI-\lambda_3S, & \dot E&=\frac{\lambda_1}{N}SE+\frac{\lambda_2}{N}SI-(\alpha_1+\alpha_2)E,\\ \dot I&=\alpha_1E-(\beta_1+\beta_2)I, & \dot E_r&=\alpha_2E,\quad \dot R=\beta_1I,\quad \dot D=\beta_2I,\quad \dot Q=\lambda_3S,\end{aligned}$$

with contact rates $\lambda_1$ (with exposed) and $\lambda_2$ (with infected), quarantine rate $\lambda_3\ge0$, incubation rate $\alpha_1$, recovery rate of exposed $\alpha_2$, recovery rate $\beta_1$ and death rate $\beta_2$, all positive except possibly $\lambda_3$. Nonnegative initial data give unique global nonnegative solutions, and $S(t)\le S(0)e^{-\lambda_3t}$.

**Basic reproduction number.** The next-generation computation at the disease-free state $S=N$ with infected compartments $(E,I)$ gives

$$R_0=\frac{\lambda_1(\beta_1+\beta_2)+\alpha_1\lambda_2}{(\alpha_1+\alpha_2)(\beta_1+\beta_2)}=\frac{\lambda_1}{\alpha_1+\alpha_2}+\frac{\alpha_1}{\alpha_1+\alpha_2}\cdot\frac{\lambda_2}{\beta_1+\beta_2},$$

the secondary infections produced during the exposed stage plus those produced after progressing to the symptomatic stage. The effective reproduction number is $R_0(t)=R_0\,S(t)/N$, which quarantine drives down exponentially.

**Theorem.** If $R_0<1$, then $E(t)\to0$ and $I(t)\to0$ as $t\to\infty$.

## Expansion

Take $V=\lambda_2I+(\beta_1+\beta_2)E\ge0$. Using $S\le N$,

$$\dot V\le\big(\alpha_1\lambda_2+\lambda_1(\beta_1+\beta_2)-(\alpha_1+\alpha_2)(\beta_1+\beta_2)\big)E=-cE,$$

with $c=(\alpha_1+\alpha_2)(\beta_1+\beta_2)(1-R_0)>0$ when $R_0<1$. Hence $V$ is nonincreasing and $\int_0^\infty E\,dt\le V(0)/c<\infty$. Since $\dot E$ is bounded, $E\to0$ (Barbalat's lemma), and then $\dot I=\alpha_1E-(\beta_1+\beta_2)I$ gives $I\to0$. (The source states $\dot V\le -cV$; that step needs a separate bound on $I$, so the integrability argument above is the reliable route to the same conclusion.) With $\lambda_3=0$, integrating the $S$ equation shows that the cumulative force of infection equals $S(0)-S(t)$, which is how the source argues that quarantine limits the final epidemic size.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Sources

- H. Ben Fredj and F. Chérif, *Novel Corona virus disease infection in Tunisia: mathematical model and the impact of the quarantine strategy*, arXiv:2004.10321 (2020), Section 2 (model) and Sections 3.2–3.3 (reproduction number, extinction theorem, quarantine). <https://doi.org/10.48550/arXiv.2004.10321>

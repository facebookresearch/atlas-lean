# Community and hospital reproduction numbers of an SEIAHR model with lockdown

**Model.** The population is split into susceptible $S$, exposed $E$, symptomatic $I_S$, asymptomatic $I_A$, hospitalized and notified $H$, and recovered $R$, with $N=S+E+I_S+I_A+H+R$. Births occur at rate $\Pi$ and natural deaths at rate $\mu$. Community transmission has rate $\beta_1$. Hospitalized cases transmit at rate $\beta_2$, but only to a fraction $\rho$ of susceptibles. Exposed individuals progress at rate $\sigma$, a fraction $\kappa$ of them becoming symptomatic. Symptomatic cases are hospitalized at rate $\tau$. Recovery rates are $\gamma_1,\gamma_2,\gamma_3$ and the disease death rate in hospital is $\delta$. Then

$$\begin{aligned}
\dot S&=\Pi-\frac{\beta_1S(I_S+I_A)}{N}-\frac{\beta_2\rho SH}{N}-\mu S, &
\dot E&=\frac{\beta_1S(I_S+I_A)}{N}+\frac{\beta_2\rho SH}{N}-(\mu+\sigma)E,\\
\dot I_S&=\kappa\sigma E-(\tau+\mu+\gamma_1)I_S, &
\dot I_A&=(1-\kappa)\sigma E-(\mu+\gamma_2)I_A,\\
\dot H&=\tau I_S-(\gamma_3+\delta+\mu)H, &
\dot R&=\gamma_1I_S+\gamma_2I_A+\gamma_3H-\mu R .
\end{aligned}$$

Lockdown is modeled by a class $L$: susceptibles enter it at rate $l$ and return at rate $\omega$. Locked-down individuals do not mix, so all incidence terms use $N-L$ in place of $N$.

**Statement.**

1. The nonnegative orthant is invariant, and $\Omega=\{S+E+I_S+I_A+H+R\le\Pi/\mu\}$ is positively invariant and attracting.
2. The basic reproduction number is $\mathcal R_0=\mathcal R_C+\mathcal R_H$, with community part

$$\mathcal R_C=\frac{\beta_1\kappa\sigma}{(\mu+\sigma)(\gamma_1+\mu+\tau)}+\frac{\beta_1(1-\kappa)\sigma}{(\mu+\sigma)(\mu+\gamma_2)}$$

and hospital part

$$\mathcal R_H=\frac{\beta_2\,\kappa\,\rho\,\sigma\,\tau}{(\mu+\sigma)(\gamma_1+\mu+\tau)(\delta+\gamma_3+\mu)} .$$

Because the lockdown class does not mix, $\mathcal R_0$ is the same with and without lockdown. Lockdown reduces case counts by depleting $S$, not by changing $\mathcal R_0$.
3. The disease-free equilibrium is locally asymptotically stable if $\mathcal R_0<1$ and unstable if $\mathcal R_0>1$. It is globally asymptotically stable in $\Omega$ whenever $\mathcal R_0<1$.
4. There is a unique endemic equilibrium when $\mathcal R_0>1$ and none when $\mathcal R_0\le1$, so no backward bifurcation occurs.

## Expansion

In the next-generation construction the infected compartments are $(E,I_S,I_A,H)$ and new infections enter only $E$. Then $FV^{-1}$ has rank one, and $\mathcal R_0$ is the sum, over the three infectious routes, of (probability of reaching the stage) $\times$ (transmission rate) $\times$ (mean time in the stage). The factor $\sigma/(\mu+\sigma)$ is the probability of leaving $E$ alive. The fraction $\kappa$ of these become symptomatic, and $\tau/(\tau+\mu+\gamma_1)$ of symptomatic cases reach hospital, where they stay for mean time $1/(\delta+\gamma_3+\mu)$ and transmit at rate $\beta_2\rho$. Global stability for $\mathcal R_0<1$ uses the Castillo-Chavez decomposition. Split the system into uninfected states $X=(S,R)$ and infected states $I=(E,I_S,I_A,H)$, with $\dot X=T(X,I)$, $\dot I=G(X,I)$ and $G(X,0)=0$. Then check that $X^*$ is globally stable for $\dot X=T(X,0)$, and that $G(X,I)=BI-\hat G(X,I)$ with $\hat G\ge0$ on $\Omega$, because $S/N\le1$. Fitting the model to state-level notified cases separates $\mathcal R_H$ from $\mathcal R_C$, which identifies the hospital transmission rate $\beta_2$ and the hospital contact fraction $\rho$ as controllable drivers of outbreak risk.

The statements are the positivity proposition and boundedness lemma, the DFE stability lemma and theorem, and the endemic-equilibrium theorem of the source's supplementary analysis, together with its main-text $\mathcal R_0$ decomposition.

## Proof depends on

- [Threshold theorem, stability half, conditional decay form](../../next-generation-matrix-and-the-basic-reproductio/global-solution-decay-of-r0-lt-one.md)
- [Threshold theorem, instability half, spectral form](../../next-generation-matrix-and-the-basic-reproductio/exists-re-pos-jacobian-of-one-lt-r0.md)
- [Lyapunov's indirect method, instability](../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/exists-unstable-of-has-fderiv-at.md)

## Sources

- T. Sardar, S. Rana, "Effective lockdown and role of hospital-based COVID-19 transmission in some Indian states: An outbreak risk analysis", arXiv:2005.01149 (2020). <https://doi.org/10.48550/arXiv.2005.01149>

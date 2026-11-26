# Backward bifurcation in a state-dependent threshold-delay COVID-19 model

**Model.** Susceptible $S$, asymptomatic infectious $A$ and unreported symptomatic $I_u$ individuals in a population of size $N$ with recruitment $\pi_S$, natural death rate $d_S$, transmission rate $\alpha$, exit rate $\delta$ from $A$, progression rate $\delta_1$ from $A$ to $I_u$, recovery rate $\mu$ and disease death rate $d$ evolve by

$$
\begin{aligned}
S'(t)&=\pi_S-\alpha S(t)\bigl(A(t)+I_u(t)\bigr)/N-d_SS(t),\\
A'(t)&=\alpha e^{-\eta\,\sigma(t)}S(t-\sigma(t))\bigl(A(t-\sigma(t))+I_u(t-\sigma(t))\bigr)/N-(\delta+d_S)A(t),\\
I_u'(t)&=\delta_1A(t)-(\mu+d+d_S)I_u(t),
\end{aligned}
$$

with state-dependent delay $\sigma(t)=\tau\bigl(A(t)+I_u(t)\bigr)$ for a smooth threshold-delay function $\tau\ge0$, and $e^{-\eta\sigma}$ the probability of surviving the delay period. Writing $k=(\mu+d+\delta_1+d_S)/(\mu+d+d_S)$ and $\nu(y)=\tau(ky)$, an endemic equilibrium $(\tilde S,\tilde A,\tilde I_u)$ satisfies $\tilde I_u=\delta_1\tilde A/(\mu+d+d_S)$, $\tilde S=\pi_S/(\alpha k\tilde A/N+d_S)$ and $\chi(\tilde A)=\kappa$, where

$$
\chi(y)=\frac{\pi_S\,\alpha\,e^{-\eta\nu(y)}\,(\mu+d+\delta_1+d_S)}{\alpha k y/N+d_S}, \qquad \chi(0)=R_c\,\kappa ,
$$

$\kappa>0$ is a constant independent of $y$, and $R_c$ is the control reproduction number (proportional to $\alpha e^{-\eta\tau(0)}$). Also $\chi(y)\to0$ as $y\to\infty$, and $\chi'(y)$ has the sign of $-W(y)$ with $W(y)=\eta\nu'(y)\bigl(\alpha ky/N+d_S\bigr)+\alpha k/N$.

**Proposition (equilibria).** The disease-free equilibrium $\bar E=(\pi_S/d_S,0,0)$ always exists. If $W>0$ (so $\chi$ is strictly decreasing), there is no endemic equilibrium for $R_c\le1$ and exactly one for $R_c>1$. If $R_c<1$ but $\chi(A^*)>\kappa$ for some $A^*>0$, there are at least two endemic equilibria. If $R_c\le1$ and $\chi<\kappa$ everywhere, there is none.

**Theorem (stability and bifurcation).** $\bar E$ is locally asymptotically stable for $R_c<1$ and unstable for $R_c>1$. If $W(\tilde A)>0$, a forward transcritical bifurcation occurs at $R_c=1$: for $R_c>1$ near $1$ the unique endemic equilibrium is locally asymptotically stable. If instead $\chi$ rises above $\kappa$ while $R_c<1$, the system undergoes a **backward bifurcation** at $R_c=1$: for $R_c<1$ near $1$ the disease-free equilibrium coexists with a locally asymptotically stable endemic equilibrium and an unstable one, so reducing $R_c$ just below $1$ (for instance by partially lifting lockdown and then tightening it) need not eliminate the epidemic.

## Expansion

Endemic equilibria are the intersections of the curve $\chi$ with the horizontal level $\kappa$. Since $\chi(0)=R_c\kappa$ and $\chi\to0$, a decreasing $\chi$ crosses $\kappa$ once exactly when $R_c>1$. When the threshold delay $\tau$ decreases fast enough with infection prevalence ($\nu'<0$ large, making $W<0$ on an interval), $e^{-\eta\nu(y)}$ grows with $y$ and $\chi$ can exceed $\kappa$ at intermediate $y$ although $\chi(0)<\kappa$; then $\chi=\kappa$ has two roots $A^m<A^M$, the smaller unstable and the larger stable, which is the backward-bifurcation picture. Linearization of the state-dependent delay system at an equilibrium reduces to a constant-delay characteristic equation with delay $\tau$ evaluated at the equilibrium plus a correction from $\tau'$, from which the stability claims follow.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Sources

- R. Qesmi and A. Hammoumi, "Lifting lockdown control measure assessment: from finite to infinite-dimensional epidemic models for COVID-19", arXiv:2012.05998 (2020), section "COVID-19 model with threshold-type delay" (system for $S,A,I_u$; equilibrium proposition; stability, transcritical and backward bifurcation theorems), <https://doi.org/10.48550/arXiv.2012.05998>.

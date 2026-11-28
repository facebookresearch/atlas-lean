# Equilibria and global stability of the SIRS model with a vaccine-confidence ceiling

**Model (SIRS-$V_\kappa$).** Population fractions $S,I,R,V\ge0$ with $S+I+R+V=1$ evolve by

$$\dot S=-\beta SI-\rho\Bigl(1-\frac V\kappa\Bigr)S+\omega R,\qquad \dot I=\beta SI-\gamma I,$$

$$\dot R=\gamma I-\omega R-\rho\Bigl(1-\frac V\kappa\Bigr)R,\qquad \dot V=\rho\Bigl(1-\frac V\kappa\Bigr)(S+R),$$

with transmission rate $\beta$, recovery rate $\gamma$, waning-immunity rate $\omega$, vaccine roll-out rate $\rho$, all positive, and *vaccine confidence* $\kappa>0$: the vaccinated fraction behaves like a logistic population with carrying capacity $\kappa$, and $1/\kappa$ measures vaccine hesitancy. Let $\underline\kappa=\min\{1,\kappa\}$; if $V(t_0)\in[0,\underline\kappa]$ then $V(t)\in[0,\underline\kappa]$ and the simplex is invariant.

**Theorem.**

1. $\mathcal{R}_0=\beta/\gamma$, and the effective reproduction number satisfies $\mathcal{R}_t\le(1-V(t))\,\beta/\gamma$.
2. There is always a unique disease-free equilibrium $(S,I,R,V)=(1-\underline\kappa,0,0,\underline\kappa)$.
3. An endemic equilibrium exists if and only if $\kappa<1-\gamma/\beta$, i.e. $(1-\kappa)\beta/\gamma>1$; it is then unique, strictly positive, and equal to

$$\Bigl(\frac\gamma\beta,\ \frac{1-\kappa-\gamma/\beta}{1+\gamma/\omega},\ \frac{1-\kappa-\gamma/\beta}{1+\omega/\gamma},\ \kappa\Bigr),\qquad \frac{I}{R}=\frac\omega\gamma .$$

4. The disease-free equilibrium is globally asymptotically stable if and only if $(1-\kappa)\,\beta/\gamma\le1$.

Thus the herd-immunity condition is a condition on confidence, not on roll-out speed: eradication requires $\kappa\ge1-1/\mathcal{R}_0$, and below that confidence level the endemic infected level $I^*=(1-\kappa-\gamma/\beta)/(1+\gamma/\omega)$ of item 3 does not depend on the roll-out rate $\rho$.

## Expansion

1. $V$ increases monotonically toward $\underline\kappa$ and every equilibrium has $V=\underline\kappa$ or $S+R=0$; with $I=0$ this forces the disease-free point.
2. At an endemic equilibrium, $\dot I=0$ gives $S=\gamma/\beta$, $\dot V=0$ with $S+R>0$ gives $V=\kappa$, and $\dot R=0$ gives $I/R=\omega/\gamma$; the simplex constraint fixes $I$ and $R$, positive iff $1-\kappa-\gamma/\beta>0$.
3. For global stability, $V(t)\to\underline\kappa$, so eventually $S\le1-\kappa+\epsilon$ and $\dot I\le(\beta(1-\kappa+\epsilon)-\gamma)I$; when $(1-\kappa)\beta\le\gamma$ a Lyapunov / asymptotically autonomous argument gives $I\to0$, while if $(1-\kappa)\beta>\gamma$ the disease-free point is unstable.

## Sources

- C. H. Leung, M. E. Gibbs, P. E. Paré, *The impact of vaccine hesitancy on epidemic spreading*, arXiv:2109.14000 (Lemma 2.1, Propositions 1–3, Lemma 3.2 and Theorem 1). <https://doi.org/10.48550/arXiv.2109.14000> Published version: 2022 American Control Conference (ACC) (2022) 3656–3661, <https://doi.org/10.23919/acc53348.2022.9867327>.

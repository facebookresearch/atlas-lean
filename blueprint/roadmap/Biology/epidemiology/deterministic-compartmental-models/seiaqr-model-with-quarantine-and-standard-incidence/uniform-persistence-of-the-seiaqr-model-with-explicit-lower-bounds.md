# Uniform persistence of the SEIAQR quarantine model with explicit lower bounds

**Model.** Let $S, E, I, A, Q, R \ge 0$ be the susceptible, exposed, symptomatic, asymptomatic, quarantined and recovered classes, $N = S+E+I+A+Q+R$, and consider

$$\begin{aligned}
\dot S &= \lambda - \beta\frac{S}{N}(aE + I + bA) - dS, &\quad \dot E &= \beta\frac{S}{N}(aE + I + bA) - (c+d)E,\\
\dot I &= pcE - (q_1 + r_1 + d)I, & \dot A &= (1-p)cE - (q_2 + r_2 + d)A,\\
\dot Q &= q_1 I + q_2 A - (r_3 + d)Q, & \dot R &= r_1 I + r_2 A + r_3 Q - dR,
\end{aligned}$$

with all parameters positive and $p \in (0,1)$: $\lambda$ is recruitment, $d$ natural death, $\beta$ transmission, $a, b$ the relative infectiousness of exposed and asymptomatic individuals, $c$ the exit rate from latency, $q_i$ quarantine and $r_i$ recovery rates. With $B_i = q_i + r_i + d$ ($i=1,2$), the **control reproduction number** is

$$\mathcal R_c = \frac{a\beta}{c+d} + \frac{pc\beta}{(c+d)B_1} + \frac{bc\beta(1-p)}{(c+d)B_2}.$$

The disease-free equilibrium is $V^0 = (\lambda/d, 0,0,0,0,0)$.

**Equilibria.** The system has a unique endemic equilibrium $V^* = (S^*, E^*, I^*, A^*, Q^*, R^*)$ if and only if $\mathcal R_c > 1$; then $\mathcal R_c = S^0/S^*$ with $S^0 = \lambda/d$, and $E^* = \lambda(\mathcal R_c - 1)/((c+d)\mathcal R_c)$.

**Local stability.** $V^0$ is locally asymptotically stable if $\mathcal R_c < 1$, linearly stable if $\mathcal R_c = 1$, and unstable if $\mathcal R_c > 1$.

**Theorem (uniform persistence with explicit bound).** Let $\mathcal R_c > 1$ and $m = \max\{a, b, 1\}$. For every $\theta \in (0,1)$ there is an explicit time $T = T(\theta)$, built from the model parameters, such that every solution with positive initial data satisfies

$$\liminf_{t\to\infty} E(t) \ge \nu := \theta E^* e^{(ad/m - c - d)T} = \frac{\theta\lambda(\mathcal R_c - 1)}{(c+d)\mathcal R_c}\, e^{(ad/m - c - d)T},$$

and consequently

$$\liminf S \ge \frac{\lambda}{\beta m},\quad \liminf I \ge \frac{pc\nu}{B_1},\quad \liminf A \ge \frac{(1-p)c\nu}{B_2},\quad \liminf Q \ge \frac{q_1\liminf I + q_2 \liminf A}{r_3 + d},$$

with an analogous bound for $R$. In particular the epidemic is uniformly persistent whenever $\mathcal R_c > 1$.

## Proof sketch

The approach replaces the usual abstract persistence theory by a quantitative contradiction argument. If $E(t) \le \theta E^*$ on a long interval, then the fraction $S/N$ is eventually pushed above a level at which the linear growth factor of $(E, I, A)$ exceeds one (because $\mathcal R_c = S^0/S^* > 1$), so $E$ must grow exponentially and leave the band; combining this with a lower bound on how fast $E$ can decay (rate at most $c+d$, partly compensated by the $aE$ term in the incidence) gives an explicit time window $T$ and the explicit floor $\nu$. The bounds for $I$, $A$, $Q$, $R$ then follow by comparison in the linear equations. The same technique sharpens persistence bounds for related delay models.

## Sources

- Song-bai Guo, Yu-ling Xue, Xi-liang Li and Zuo-huan Zheng, "A Novel Analysis Approach of Uniform Persistence for an Epidemic Model with Quarantine and Standard Incidence Rate", *Acta Mathematicae Applicatae Sinica, English Series* 40 (2024), 695–707, <https://doi.org/10.1007/s10255-023-1078-y>. Preprint version: arXiv:2205.15560 (2022), model (2.1), Lemma 3.1, Theorem 4.1, Corollary 4.1, Theorems 4.2–4.3, <https://doi.org/10.48550/arXiv.2205.15560>.

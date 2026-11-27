# Reproduction number of the hub-and-cities SIRS model

Consider $N$ identical cities and a transportation system $T$. In city $k$, susceptibles are recruited at rate $A$, all classes die at rate $\mu$, infectives recover at rate $\gamma$, immunity wanes at rate $\eta$, and incidence is $\beta(N_k) S_k I_k$ with $N_k = S_k + I_k + R_k$; individuals enter the transportation system at rate $\phi$ (infectives at the reduced rate $\alpha\phi$, $0 \le \alpha \le 1$) and leave it at rate $p$ (the transportation efficiency), returning to each city at rate $p/N$. In transit, incidence is $\beta_T(N_T) S_T I_T$, recovery rate $\gamma_T$ and waning rate $\eta_T$:

$$
\begin{aligned}
\dot S_T &= -\beta_T S_T I_T + \eta_T R_T + \phi \textstyle\sum_j S_j - p S_T, &
\dot S_k &= A - \beta S_k I_k - \mu S_k + \eta R_k - \phi S_k + \tfrac{p}{N} S_T,\\
\dot I_T &= \beta_T S_T I_T - \gamma_T I_T + \alpha\phi \textstyle\sum_j I_j - p I_T, &
\dot I_k &= \beta S_k I_k - (\mu + \gamma + \alpha\phi) I_k + \tfrac{p}{N} I_T,\\
\dot R_T &= \gamma_T I_T - \eta_T R_T + \phi \textstyle\sum_j R_j - p R_T, &
\dot R_k &= \gamma I_k - (\eta + \mu + \phi) R_k + \tfrac{p}{N} R_T .
\end{aligned}
$$

Contact rates satisfy $\beta(\cdot), \beta_T(\cdot) > 0$ and are non-increasing in population size. The disease-free equilibrium has $S_k = A/\mu$ and $S_T = \phi N A/(p\mu)$; write $\beta = \beta(A/\mu)$, $\beta_T = \beta_T(\phi N A/(p\mu))$ for the contact rates there, and

$$R^{*} = \frac{\beta A}{\mu(\mu + \gamma)}$$

for the reproduction number of an isolated city.

**Theorem.** Let $R_0$ be the spectral radius of the next-generation matrix of the infected compartments $(I_T, I_1, \dots, I_N)$. The disease-free equilibrium is locally asymptotically stable if $R_0 < 1$ and unstable if $R_0 > 1$. Moreover:

1. (fast transit) if $\beta_T(y)/y \to 0$ as $y \to 0^+$, then $R_0 \to R^{*}$ as $p \to \infty$, so for large $p$ stability is decided by $R^{*}$;
2. (few travellers) $R_0 \to R^{*}$ as $\phi \to 0^+$;
3. (no infected travellers) as $\alpha \to 0^+$, $R_0 \to \max\big\{R^{*},\ \beta_T A N \phi / (\mu p(\gamma_T + p))\big\}$, so transmission in transit alone can sustain spread even when $R^{*} < 1$;
4. (clean transit) as $\beta_T \to 0$,

    $$R_0 \to \frac{\beta A}{\mu}\cdot \frac{1}{\mu + \gamma + \alpha\phi\,\gamma_T/(\gamma_T + p)} < R^{*},$$

    so a transportation system with little internal transmission lowers the reproduction number below its isolated-city value.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

The threshold statement is the van den Driessche–Watmough theorem. For identical cities the inverse next-generation structure is an arrow matrix: one eigenvalue $\mu(\mu + \gamma + \alpha\phi)/(\beta A)$ of multiplicity $N - 1$ (antisymmetric modes across cities) and two roots of a quadratic for the symmetric city–hub mode, which gives $R_0$ in closed form. The limit 4 has a random-walk reading: an infective in a city infects at rate $\beta A/\mu$ for an expected time $1/(\mu + \gamma + \alpha\phi)$ per visit, leaves for the hub with probability $\alpha\phi/(\mu+\gamma+\alpha\phi)$ and returns still infectious with probability $p/(\gamma_T + p)$; summing the geometric series of visits gives the formula, and recovery during transit is what makes it smaller than $R^{*}$. Limits 1 and 2 hold because transmission in transit vanishes when time in transit or the number of travellers goes to zero. With non-identical cities only bounds on $R_0$ are available, and city sizes enter through travellers being distributed in proportion to $A_k$.

## Sources

- F. Xu, C. Connell McCluskey, R. Cressman, "Spatial spread of an epidemic through public transportation systems with a hub", Mathematical Biosciences 246(1) (2013) 164–175, Eqs. (1), (8), (22)–(32), Theorems 1–4, <https://doi.org/10.1016/j.mbs.2013.08.014>, PMCID PMC7094585.

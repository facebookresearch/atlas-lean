# Basic reproduction number and endemic equilibrium of the SEQIR model

Consider the system

$$\begin{aligned}
S' &= A - kSE + b_1 Q - dS - pMS, \\
E' &= kSE - (b_2 + \alpha + \sigma + d)E, \\
Q' &= b_2 E - (b_1 + c + d)Q, \\
I' &= \alpha E + cQ - (\eta + d + \delta)I, \\
R' &= \eta I + \sigma E - dR + pMS,
\end{aligned}$$

with $k = \beta(1-\rho_1)(1-\rho_2)$, where $A > 0$ is recruitment, $\beta > 0$ the transmission rate, $\rho_1, \rho_2 \in (0,1)$ the precaution fractions of susceptibles and exposed, $b_2, \alpha, \sigma > 0$ the rates from $E$ to quarantine, to hospitalized infection and to recovery, $b_1, c > 0$ the rates from $Q$ back to $S$ and on to $I$, $\eta > 0$ recovery, $d > 0$ natural and $\delta \ge 0$ disease mortality, and $pM \ge 0$ the removal rate of susceptibles by the lockdown policy. Hospitalized individuals ($I$) are isolated and do not transmit.

Write $K = b_2 + \alpha + \sigma + d$, $m = b_1 + c + d$ and $D = b_2(c+d) + (\alpha + \sigma + d)\,m$. Then:

1. The disease-free equilibrium is $E_0 = \bigl(S_0, 0, 0, 0, pMA/(d(d+pM))\bigr)$ with $S_0 = A/(d + pM)$, and the basic reproduction number (spectral radius of the next-generation matrix with infected compartments $E, Q, I$) is

$$\mathcal R_0 \;=\; \frac{kA}{(d + pM)\,K} \;=\; \frac{\beta(1-\rho_1)(1-\rho_2)\,A}{(d + pM)(b_2 + \alpha + \sigma + d)} .$$

2. An endemic equilibrium with $E^* > 0$ exists if and only if $\mathcal R_0 > 1$, and it is unique:

$$S^* = \frac{K}{k}, \quad E^* = \frac{m\,\bigl(kA - (d+pM)K\bigr)}{k\,D}, \quad Q^* = \frac{b_2 E^*}{m}, \quad I^* = \frac{\alpha E^* + cQ^*}{\eta + d + \delta}, \quad R^* = \frac{\eta I^* + \sigma E^* + pMS^*}{d}.$$

3. The disease-free equilibrium is locally asymptotically stable if $\mathcal R_0 < 1$ and unstable if $\mathcal R_0 > 1$; at $\mathcal R_0 = 1$ the two equilibria exchange stability (transcritical bifurcation).

Since $\mathcal R_0$ is decreasing in $\rho_1$, $\rho_2$ and $pM$, precautions and lockdown lower the threshold directly; the critical policy intensity is $pM = kA/K - d$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

At the disease-free state $E = Q = I = 0$, so $S' = 0$ gives $S_0 = A/(d+pM)$. Only $E$ receives new infections, so $F$ has the single nonzero entry $kS_0$ in position $(E, E)$, and $V$ is lower triangular with diagonal $(K, m, \eta + d + \delta)$; hence $\rho(FV^{-1}) = kS_0/K$. At an endemic state $E' = 0$ with $E \ne 0$ forces $S^* = K/k$; $Q' = 0$ gives $Q^* = b_2E^*/m$; and substituting into $S' = 0$ gives $E^*(K - b_1b_2/m) = A - (d+pM)K/k$. Because $Km - b_1b_2 = D > 0$, $E^* > 0$ exactly when $kA > (d+pM)K$, i.e. $\mathcal R_0 > 1$. Local stability of $E_0$ follows from the van den Driessche–Watmough theorem, since the uninfected block of the Jacobian has eigenvalues $-(d+pM)$ and $-d$.

## Sources

- M. Mandal, S. Jana, S. K. Nandi, A. Khatua, S. Adak, T. K. Kar, "A model based study on the dynamics of COVID-19: Prediction and control", *Chaos, Solitons & Fractals* 136 (2020) 109889, Sections 2 and 3.2–3.4 (system (1), Equation (3), Theorems 3.2 and 3.3), <https://doi.org/10.1016/j.chaos.2020.109889> (PMC7218394).

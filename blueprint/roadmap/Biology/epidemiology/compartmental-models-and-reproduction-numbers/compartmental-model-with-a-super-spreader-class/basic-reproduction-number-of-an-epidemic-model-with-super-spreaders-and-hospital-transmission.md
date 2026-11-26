# Basic reproduction number of an epidemic model with super-spreaders and hospital transmission

**Setting.** A closed population of size $N$ is split into susceptible $S$, exposed $E$, symptomatic infectious $I$, super-spreaders $P$, asymptomatic $A$, hospitalized $H$, recovered $R$ and dead $F$:

$$
\begin{aligned}
S' &= -\frac{S}{N}\bigl(\beta I + l\beta H + \beta' P\bigr), &
E' &= \frac{S}{N}\bigl(\beta I + l\beta H + \beta' P\bigr) - \kappa E,\\
I' &= \kappa\rho_1 E - (\gamma_a + \gamma_i + \delta_i) I, &
P' &= \kappa\rho_2 E - (\gamma_a + \gamma_i + \delta_p) P,\\
A' &= \kappa(1 - \rho_1 - \rho_2) E, &
H' &= \gamma_a (I + P) - (\gamma_r + \delta_h) H,\\
R' &= \gamma_i (I + P) + \gamma_r H, &
F' &= \delta_i I + \delta_p P + \delta_h H,
\end{aligned}
$$

with positive rates, $\rho_1, \rho_2 \ge 0$, $\rho_1 + \rho_2 \le 1$, and relative hospital infectiousness $l \ge 0$. Asymptomatic individuals do not transmit in this model. Write $\varpi_i = \gamma_a + \gamma_i + \delta_i$, $\varpi_p = \gamma_a + \gamma_i + \delta_p$, $\varpi_h = \gamma_r + \delta_h$.

**Proposition.**

1. The equations for $A$, $R$ and $F$ decouple: $A$, $R$, $F$ are integrals of $E$, $I + P$, $H$, and $S = N - (E + I + P + A + H + R + F)$.
2. With infected compartments $(E, I, P, H)$, the next-generation matrix at the disease-free equilibrium $(N, 0, \dots, 0)$ has spectral radius

$$R_0 = \frac{\beta\rho_1\,(\gamma_a l + \varpi_h)}{\varpi_i\,\varpi_h} + \frac{(\beta\gamma_a l + \beta'\varpi_h)\,\rho_2}{\varpi_p\,\varpi_h} .$$

3. (Theorem 1) The disease-free equilibrium is locally asymptotically stable if $R_0 < 1$ and unstable if $R_0 > 1$.
4. $R_0$ is linear in $(\rho_1, \rho_2)$ and in $(\beta, \beta')$; consequently the normalized sensitivity indices $\Upsilon_\theta = (\partial R_0/\partial \theta)(\theta/R_0)$ satisfy $\Upsilon_{\rho_1} + \Upsilon_{\rho_2} = 1$ and $\Upsilon_\beta + \Upsilon_{\beta'} = 1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

(1) is direct integration and conservation of $N$. (2): an exposed individual becomes symptomatic with probability $\rho_1$, then infects at rate $\beta$ for mean time $1/\varpi_i$ and is hospitalized with probability $\gamma_a/\varpi_i$, after which it infects at rate $l\beta$ for mean time $1/\varpi_h$, giving $\beta(\varpi_h + \gamma_a l)/(\varpi_i\varpi_h)$; the super-spreader branch gives $(\beta'\varpi_h + \beta\gamma_a l)/(\varpi_p\varpi_h)$. Because only $E$ receives new infections, $F V^{-1}$ has rank one and its spectral radius is this expected sum, which agrees with the van den Driessche–Watmough computation in the source. (3) follows from the Liénard–Chipart conditions on the characteristic polynomial of the Jacobian in $(E, I, P, H)$, whose coefficients the authors rewrite in terms of $1 - R_0$. (4) is Euler's identity for functions homogeneous of degree one in the given pair of parameters. With the parameter values fitted to Wuhan case data in the source, $R_0 = 0.945$.

## Sources

- F. Ndaïrou, I. Area, J. J. Nieto, D. F. M. Torres, "Mathematical modeling of COVID-19 transmission dynamics with a case study of Wuhan", Chaos, Solitons & Fractals 135 (2020) 109846, Eqs. (1)–(7), Theorem 1 and Section 4, <https://doi.org/10.1016/j.chaos.2020.109846> (PMC7184012).
- P. van den Driessche, J. Watmough, "Reproduction numbers and sub-threshold endemic equilibria for compartmental models of disease transmission", Mathematical Biosciences 180 (2002) 29–48, <https://doi.org/10.1016/S0025-5564(02)00108-6>.

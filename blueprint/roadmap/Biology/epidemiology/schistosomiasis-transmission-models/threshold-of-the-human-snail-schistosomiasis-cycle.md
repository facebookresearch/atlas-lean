# Threshold of the human-snail schistosomiasis cycle

**Model.** Humans are susceptible $S_H$ or infected $I_B$; snails are susceptible $S_S$ or infected $I_S$; free-living larvae are miracidia $M$ (shed by humans, infect snails) and cercariae $P$ (shed by snails, infect humans). With recruitment $\Lambda_H, \Lambda_S$, natural mortalities $\mu_H, \mu_S, \mu_M, \mu_P$, disease-induced mortalities $d_B, d_S$, treatment (recovery) rate $\omega$, and saturating forces of infection

$$\lambda_P = \frac{\beta_P P}{P_0 + \epsilon P}, \qquad \lambda_M = \frac{\beta_M M}{M_0 + \epsilon M},$$

the schistosomiasis-only system is

$$\begin{aligned}
S_H' &= \Lambda_H + \omega I_B - (\lambda_P + \mu_H) S_H, & I_B' &= \lambda_P S_H - (\mu_H + \omega + d_B) I_B,\\
M' &= N_E \gamma\, I_B - \mu_M M, & P' &= \theta I_S - \mu_P P,\\
S_S' &= \Lambda_S - (\lambda_M + \mu_S) S_S, & I_S' &= \lambda_M S_S - (\mu_S + d_S) I_S,
\end{aligned}$$

with all parameters positive ($N_E \gamma$ is the effective miracidial output per infected human, $\theta$ the cercarial output per infected snail). The disease-free equilibrium is $(\Lambda_H/\mu_H, 0, 0, \Lambda_S/\mu_S, 0, 0)$.

**Threshold.** Define

$$\mathcal R_H = \frac{\beta_P N_E \gamma \Lambda_H}{\mu_M \mu_H P_0 (\mu_H + \omega + d_B)}, \qquad \mathcal R_S = \frac{\beta_M \theta \Lambda_S}{\mu_P \mu_S M_0 (\mu_S + d_S)}, \qquad \mathcal R_B = \mathcal R_H \mathcal R_S .$$

**Theorem.** The disease-free equilibrium is locally asymptotically stable if $\mathcal R_B < 1$ and unstable if $\mathcal R_B > 1$. Moreover it is globally asymptotically stable in the biologically feasible region whenever $\mathcal R_B < 1$. Treatment lowers the threshold: the elasticity is $\frac{\omega}{\mathcal R_B}\frac{\partial \mathcal R_B}{\partial \omega} = -\frac{\omega}{\mu_H + \omega + d_B} < 0$.

## Expansion

$\mathcal R_B$ is the gain of one full transmission cycle at the disease-free state: an infected human sheds $N_E\gamma/(\mu_H+\omega+d_B)$ miracidia over the infection, each surviving $1/\mu_M$ and infecting snails at per-capita rate $\beta_M \Lambda_S/(\mu_S M_0)$; an infected snail sheds $\theta/(\mu_S + d_S)$ cercariae, each surviving $1/\mu_P$ and infecting humans at rate $\beta_P \Lambda_H/(\mu_H P_0)$. Multiplying these four factors gives $\mathcal R_H \mathcal R_S$. Because the next-generation operator is cyclic, its spectral radius is below one exactly when this cycle product is, which yields the local result. For global stability, split the state into uninfected $X$ and infected $Z$ and write $Z' = AZ - \hat G(X,Z)$ with $A$ the linearization at the disease-free state. The components of $\hat G$ are $\beta_P P\,(\Lambda_H/(\mu_H P_0) - S_H/(P_0+\epsilon P))$ and $\beta_M M\,(\Lambda_S/(\mu_S M_0) - S_S/(M_0 + \epsilon M))$, both nonnegative because $S_H \le \Lambda_H/\mu_H$ and $S_S \le \Lambda_S/\mu_S$ on the attracting region; the Castillo-Chavez–Feng–Huang criterion then applies. Without treatment ($\omega = 0$) the same expression gives the uncontrolled number $\mathcal R_{0B}$.

## Sources

- S. Mushayabasa, C. P. Bhunu, "Modeling schistosomiasis and HIV/AIDS codynamics", Computational and Mathematical Methods in Medicine (2011) 846174, Section 3.2, Equations (24)-(29), (31), Theorems 3-5, <https://doi.org/10.1155/2011/846174>, PMCID PMC3042740.

# Virus reproduction number split between tumour and normal cells

**Model.** Let $N_S, N_I$ be uninfected and infected normal cells, $T_S, T_I$ uninfected and infected tumour cells, $V$ free virus, $Y_T$ tumour-specific and $Y_V$ virus-specific immune cells, with a delay $\tau \ge 0$ in the antiviral response and all parameters positive:

$$\begin{aligned}
N_S' &= r_N N_S \Bigl(1 - \tfrac{N_S + N_I}{K_N}\Bigr) - \beta_N N_S V, \qquad
T_S' = r_T T_S \Bigl(1 - \tfrac{T_S + T_I}{K_T}\Bigr) - \beta_T T_S V - \gamma_T \tfrac{Y_T}{h + Y_T} T_S,\\
N_I' &= \beta_N N_S V - \lambda_N N_I - \gamma_V Y_V N_I, \qquad
T_I' = \beta_T T_S V - \lambda_T T_I - \gamma_T \tfrac{Y_T}{h + Y_T} T_I - \gamma_V Y_V T_I,\\
V' &= b_T \lambda_T T_I + b_N \lambda_N N_I - \omega V,\\
Y_T' &= p_T \frac{T_S + T_I}{h + T_S + T_I} - \delta_T Y_T, \qquad
Y_V' = p_V \bigl(T_I(t - \tau) + N_I(t - \tau)\bigr) - \delta_V Y_V .
\end{aligned}$$

**Virus-free states.** With $N_I = T_I = V = Y_V = 0$ the model has tumour-free, tumour-only and coexistence equilibria; at the coexistence state $N_S = K_N$, $T_S = T_S^0 > 0$ is the positive root of a quadratic determined by the tumour growth, killing and immune-recruitment parameters, and $Y_T^0 = p_T T_S^0 / (\delta_T (T_S^0 + h))$.

**Reproduction number.** At a virus-free state with uninfected populations $N_S, T_S$ and tumour immunity $Y_T$,

$$\mathcal{R}_0 = \mathcal{R}_0^N + \mathcal{R}_0^T, \qquad
\mathcal{R}_0^N = \frac{b_N \beta_N N_S}{\omega}, \qquad
\mathcal{R}_0^T = \frac{b_T \beta_T T_S}{\omega} \cdot \frac{\lambda_T (Y_T + h)}{\lambda_T (Y_T + h) + \gamma_T Y_T},$$

the expected number of virions produced, through infection of normal and of tumour cells respectively, by one virion introduced into the virus-free population. The ratio $\mathcal{R}_0^T / \mathcal{R}_0^N$ measures the tumour specificity of the virus.

## Expansion

Follow one virion: it persists for mean time $1/\omega$, infecting normal cells at rate $\beta_N N_S$ and tumour cells at rate $\beta_T T_S$. An infected normal cell is removed only by lysis when $Y_V = 0$, so it releases $b_N$ virions; an infected tumour cell lyses before immune killing with probability $\lambda_T / (\lambda_T + \gamma_T Y_T/(h + Y_T))$ and then releases $b_T$ virions. Every infection cycle passes through $V$, so the virion-to-virion reproduction number is the sum of the two routes, and the virus invades the virus-free state iff $\mathcal{R}_0 > 1$. The delayed antiviral response vanishes at the virus-free state and so does not enter $\mathcal{R}_0$, although it shapes the post-invasion dynamics (oscillations, clearance). Allowing some infection of normal cells raises $\mathcal{R}_0$ through $\mathcal{R}_0^N$ and can sustain viral replication near the tumour, at the cost of lower specificity.

## Sources

- K. J. Mahasa, A. Eladdadi, L. de Pillis, R. Ouifki, "Oncolytic potency and reduced virus tumor-specificity in oncolytic virotherapy. A mathematical modelling approach", PLoS ONE 12 (2017) e0184347, model Equations (1)–(7), virus-free steady states (8)–(10) and basic reproductive number (11), <https://doi.org/10.1371/journal.pone.0184347> (PMC5608221).

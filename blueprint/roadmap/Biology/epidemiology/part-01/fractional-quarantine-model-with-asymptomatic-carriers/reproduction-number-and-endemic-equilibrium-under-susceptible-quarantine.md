# Reproduction number and endemic equilibrium under susceptible quarantine

Let $0 < \alpha \le 1$ and let $D^\alpha$ be the Caputo derivative. The population is split into susceptible $S$, symptomatic infected $I$, asymptomatic infected $A$, quarantined susceptible $S_q$, quarantined exposed $E_q$, hospitalized (isolated infected) $H$ and recovered $R$. A fraction $q \in [0,1]$ of contacts is traced and quarantined, $c$ is the contact rate, $\beta$ the transmission probability per contact, $\theta$ the relative infectiousness of asymptomatics and $\rho$ the probability of developing symptoms. With every rate raised to the power $\alpha$ so that both sides have dimension $(\text{time})^{-\alpha}$,

$$\begin{aligned}
D^\alpha S &= \Lambda - \big(c^\alpha \beta^\alpha (1-q) + c^\alpha q\big)(I + \theta^\alpha A) S + \lambda^\alpha S_q - \mu^\alpha S,\\
D^\alpha I &= \beta^\alpha c^\alpha \rho^\alpha (1-q) S (I + \theta^\alpha A) - \eta\, I,\\
D^\alpha A &= \beta^\alpha c^\alpha (1-\rho^\alpha)(1-q) S (I + \theta^\alpha A) - \xi\, A,\\
D^\alpha S_q &= (1-\beta^\alpha) c^\alpha q\, S (I + \theta^\alpha A) - (\lambda^\alpha + \mu^\alpha) S_q,\\
D^\alpha E_q &= \beta^\alpha c^\alpha q\, S (I + \theta^\alpha A) - (\delta_q^\alpha + \alpha_E^\alpha) E_q,\\
D^\alpha H &= \delta_I^\alpha I + \delta_q^\alpha E_q - (\alpha_A^\alpha + \gamma_H^\alpha) H,\\
D^\alpha R &= \gamma_I^\alpha I + \gamma_A^\alpha A + \gamma_H^\alpha H - \alpha_R^\alpha R,
\end{aligned}$$

with $\eta = \delta_I^\alpha + \gamma_I^\alpha + \alpha_I^\alpha$ and $\xi = \gamma_A^\alpha + \alpha_A^\alpha$ the exit rates of $I$ and $A$, and all parameters positive. The nonnegative orthant is positively invariant and solutions exist uniquely on $[0, \infty)$.

**Theorem (threshold).** The disease-free equilibrium is $E_0 = (\Lambda/\mu^\alpha, 0, 0, 0, 0, 0, 0)$, and the next-generation matrix gives

$$R_0 = \psi\left(\frac{\rho^\alpha}{\eta} + \frac{\theta^\alpha (1-\rho^\alpha)}{\xi}\right), \qquad \psi = \frac{\beta^\alpha c^\alpha (1-q)\,\Lambda}{\mu^\alpha}.$$

If $R_0 < 1$, $E_0$ is locally asymptotically stable. Quarantine enters only through the factor $1 - q$, so $R_0$ decreases linearly in the traced fraction and $R_0 < 1$ iff $q > 1 - 1/R_0|_{q=0}$.

**Theorem (endemic equilibrium without quarantine).** For the sub-model with $q = 0$ (so $S_q = E_q = 0$), a positive endemic equilibrium exists iff $R_0 > 1$, it is unique, and

$$S^* = \frac{\Lambda}{\mu^\alpha R_0}, \qquad I^* = \frac{\Lambda \rho^\alpha}{\eta}\left(1 - \frac{1}{R_0}\right), \qquad A^* = \frac{\Lambda (1-\rho^\alpha)}{\xi}\left(1 - \frac{1}{R_0}\right).$$

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

At $E_0$ only $I$ and $A$ generate new infections in the infectious block, so $R_0$ is the spectral radius of the rank-one matrix $F V^{-1}$ with new-infection rows proportional to $(1, \theta^\alpha)$ and $V = \operatorname{diag}(\eta, \xi)$: an introduced case is symptomatic with weight $\rho^\alpha$ for mean time $1/\eta$, or asymptomatic with weight $1-\rho^\alpha$ and relative infectiousness $\theta^\alpha$ for mean time $1/\xi$. The Jacobian at $E_0$ has five explicit negative eigenvalues ($-\lambda^\alpha - \mu^\alpha$, $-\mu^\alpha$, $-\delta_q^\alpha - \alpha_E^\alpha$, $-\alpha_R^\alpha$, $-\alpha_A^\alpha - \gamma_H^\alpha$), and the remaining $2 \times 2$ block has determinant $\eta\xi(1 - R_0)$ and negative trace when $R_0 < 1$; negative real eigenvalues satisfy the Matignon condition $|\arg \lambda| > \alpha\pi/2$ for every $\alpha \in (0,1]$. For the endemic state, write $\Phi = \beta^\alpha c^\alpha S^*(I^* + \theta^\alpha A^*)$; the $I$ and $A$ equations give $I^* = \rho^\alpha \Phi/\eta$ and $A^* = (1-\rho^\alpha)\Phi/\xi$, the infection balance gives $S^* = \Lambda/(\mu^\alpha R_0)$, and the $S$ equation gives $\Phi = \Lambda(1 - 1/R_0)$, positive iff $R_0 > 1$.

## Sources

- A. Babaei, M. Ahmadi, H. Jafari and A. Liya, "A mathematical model to examine the effect of quarantine on the spread of coronavirus", Chaos, Solitons and Fractals (2021) 110418, Eqs. (2)–(5), (21)–(22), Theorems 1–3, <https://doi.org/10.1016/j.chaos.2020.110418>, PMCID PMC7703523.
- P. van den Driessche and J. Watmough, "Reproduction numbers and sub-threshold endemic equilibria for compartmental models of disease transmission", Mathematical Biosciences 180 (2002) 29–48, <https://doi.org/10.1016/S0025-5564(02)00108-6>.

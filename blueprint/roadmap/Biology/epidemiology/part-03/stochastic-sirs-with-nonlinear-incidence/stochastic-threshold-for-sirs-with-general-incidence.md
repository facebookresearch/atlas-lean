# Stochastic threshold for SIRS with general incidence

**Model.** With recruitment $A > 0$, mortalities $\mu_1 \le \min\{\mu_2, \mu_3\}$ of susceptible, infectious and recovered individuals, recovery rate $\delta$, loss of immunity rate $\lambda$, and transmission rate perturbed as $\beta \mapsto \beta + \sigma\,\xi(t)$ with Gaussian white noise $\xi$ of intensity $\sigma > 0$, the Itô system is

$$\begin{aligned}
dS &= \big(A - \mu_1 S + \lambda R - \beta S G(I)\big)dt - \sigma S G(I)\,dB(t), \\
dI &= \big(\beta S G(I) - (\mu_2 + \delta) I\big)dt + \sigma S G(I)\,dB(t), \\
dR &= \big(\delta I - (\mu_3 + \lambda) R\big)dt,
\end{aligned}$$

where $B$ is a standard Brownian motion and the incidence function satisfies $G(0) = 0$, $0 < G(I) \le I$ for $I > 0$, $G'(0) = 1$, and $G(x)/x$ Lipschitz on $[0, A/\mu_1]$ ($G$ need not be monotone, allowing behavioural saturation). For every positive initial value there is a unique global solution that stays in $\mathbb R^3_+$ almost surely.

**Thresholds.** Let

$$R_0 = \frac{\beta A}{\mu_1(\mu_2 + \delta)}, \qquad R_0^S = R_0 - \frac{A^2\sigma^2}{2\mu_1^2(\mu_2 + \delta)} .$$

**Theorem (extinction).** If either (C1) $R_0^S < 1$ and $\sigma^2 < \beta\mu_1/A$, or (C2) $\sigma^2 > \dfrac{\beta^2}{2(\mu_2 + \delta)} = \dfrac{\beta\mu_1}{A}\cdot\dfrac{R_0}{2}$, then almost surely

$$\lim_{t\to\infty} S(t) = \frac{A}{\mu_1}, \qquad \lim_{t\to\infty} I(t) = 0, \qquad \lim_{t\to\infty} R(t) = 0,$$

and $I(t) \to 0$ exponentially fast.

**Theorem (persistence).** If $R_0^S > 1$, the infection persists in the time mean: $\liminf_{t\to\infty}\frac1t\int_0^t I(s)\,ds > 0$ almost surely (with an explicit lower bound proportional to $\Psi(A/\mu_1)$ below), and similar positive lower bounds hold for the time means of $S$ and $R$.

## Expansion

By Itô's formula,

$$d\log I = \Psi\!\Big(\frac{S\,G(I)}{I}\Big)dt + \sigma\frac{S\,G(I)}{I}\,dB, \qquad \Psi(x) = -\tfrac12\sigma^2x^2 + \beta x - (\mu_2 + \delta).$$

Since $S \le A/\mu_1$ asymptotically and $G(I) \le I$, the argument of $\Psi$ lies in $[0, A/\mu_1]$. Under (C1), $\Psi$ is increasing on $[0, \beta/\sigma^2] \supseteq [0, A/\mu_1]$, so the drift is at most $\Psi(A/\mu_1)$, which is negative exactly when $R_0^S < 1$; under (C2), $\max_x \Psi(x) = \beta^2/(2\sigma^2) - (\mu_2+\delta) < 0$. The strong law of large numbers for martingales then gives $\limsup_t \frac1t \log I(t) < 0$. Because $R_0^S < R_0$, noise can eliminate an infection that the deterministic model predicts to be endemic; for $\sigma \to 0$ the deterministic threshold $R_0 = 1$ is recovered. Under $R_0^S > 1$ the solution also has a unique ergodic stationary distribution.

## Sources

- D. Li, J. Cui, M. Liu, S. Liu, "The Evolutionary Dynamics of Stochastic Epidemic Model with Nonlinear Incidence Rate", Bulletin of Mathematical Biology 77 (2015) 1705–1743, Section 2 (model Eqs. 1–3, assumptions (H1)–(H3), Lemmas 1–2), Section 3 (conditions (C1)–(C2), $R_0^S$ Eq. 7, Theorem 1 with proof via Eq. 11) and Section 4 (Theorem 2, persistence in the mean; stationary distribution), <https://doi.org/10.1007/s11538-015-0101-9> (PMC7088780).

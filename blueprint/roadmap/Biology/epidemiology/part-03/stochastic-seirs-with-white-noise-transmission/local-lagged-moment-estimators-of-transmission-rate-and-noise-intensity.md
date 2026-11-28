# Local lagged moment estimators of transmission rate and noise intensity in the stochastic SEIRS model

**Model.** Let $S, E, I, R$ be population fractions with $S + E + I + R = 1$, birth and death rate $\delta > 0$, latency rate $\alpha > 0$, recovery rate $\nu > 0$ and loss-of-immunity rate $\gamma > 0$. The transmission rate is $\beta(t) = \beta_0(t)\,(1 + \sigma \zeta(t))$ with $\beta_0$ positive, bounded and continuous, noise intensity $\sigma > 0$, and $\zeta\,dt = dW_t$ for a standard Wiener process $W$. Interpreted in the Stratonovich sense ($\circ$), the model is

$$\begin{aligned}
dS &= (\delta - \beta_0 S I + \gamma R - \delta S)\,dt - \sigma \beta_0 S I \circ dW_t, \\
dE &= (\beta_0 S I - (\alpha + \delta) E)\,dt + \sigma \beta_0 S I \circ dW_t, \\
dI &= (\alpha E - (\nu + \delta) I)\,dt, \qquad dR = (\nu I - (\gamma + \delta) R)\,dt .
\end{aligned}$$

It has a unique global solution that stays in $[0,1]^4$ when started there.

**Proposition (Itô form).** By the Stratonovich-to-Itô drift correction $f_i = \bar f_i + \tfrac12 \sum_k g_k\, \partial g_i / \partial x_k$, the same solution satisfies the Itô system

$$\begin{aligned}
dS &= \big(\delta - \beta_0 S I + \gamma R - \delta S + \tfrac12 \sigma^2 \beta_0^2 S I^2\big)\,dt - \sigma \beta_0 S I\, dW_t, \\
dE &= \big(\beta_0 S I - (\alpha + \delta) E - \tfrac12 \sigma^2 \beta_0^2 S I^2\big)\,dt + \sigma \beta_0 S I\, dW_t,
\end{aligned}$$

with the $I$ and $R$ equations unchanged, and the quadratic variation of $E$ is $d\langle E \rangle_t = \sigma^2 \beta_0^2 S^2 I^2\, dt$.

**Moment estimators.** Observe the state at times $t_k = k\,\Delta t$ and write $\Delta E_k = E_k - E_{k-1}$, with $\mathcal{F}_{k}$ the information up to $t_k$. Fix a local window size $m_j \in \{2, \dots, M\}$. Integrating $S\,dE$ over $[t_{j - m_j + 1}, t_j]$, applying the integral mean value theorem to the continuous $\beta_0$, discretizing and taking conditional expectations gives the local estimators

$$\widehat{\beta}_{j, m_j} = \frac{\displaystyle\sum_{k = j - m_j + 1}^{j} \Big( \mathbb{E}[S_{k-1} \Delta E_k \mid \mathcal{F}_{k-1}] + \tfrac12 \mathbb{E}[\Delta E_k^2 \mid \mathcal{F}_{k-1}] + (\alpha + \delta) S_{k-1} E_{k-1} \Delta t \Big)}{\displaystyle\sum_{k = j - m_j + 1}^{j} S_{k-1}^2 I_{k-1}\, \Delta t},$$

$$\widehat{\sigma^2}_{j, m_j} = \frac{\displaystyle\sum_{k = j - m_j + 1}^{j} \mathbb{E}[\Delta E_k^2 \mid \mathcal{F}_{k-1}]}{\displaystyle\big(\widehat{\beta}_{j, m_j}\big)^2 \sum_{k = j - m_j + 1}^{j} S_{k-1}^2 I_{k-1}^2\, \Delta t},$$

in which the conditional expectations are replaced by local averages of the observed increments. Both are well defined whenever some $I_{k-1}$ in the window is positive (if $I$ vanishes on the window, so does $E$ and transmission has ended), and $S$ cannot vanish on a whole window. The window size is then chosen at each $t_j$ (local lagged adaptive generalized method of moments): among $m_j \in \{2, \dots, M\}$, pick the one whose simulated trajectories, averaged over Monte Carlo runs, minimize the squared distance to the observed state at $t_j$.

## Depends on

- [Solution of the closed SEIR system for times t ≥ 0](../../seir-epidemic-model/is-solution.md)

## Expansion

Only the $S$ and $E$ equations carry noise, with diffusion vector $g = (-h, h, 0, 0)$ where $h = \sigma\beta_0 S I$. Since $g_I = 0$, the drift correction involves only $\partial h/\partial S = \sigma\beta_0 I$: it equals $\tfrac12(-h)(-\sigma\beta_0 I) = \tfrac12\sigma^2\beta_0^2 S I^2$ for $S$ and $\tfrac12(-h)(\sigma\beta_0 I) = -\tfrac12\sigma^2\beta_0^2 S I^2$ for $E$. By Itô's formula $S\,dE = (\beta_0 S^2 I - (\alpha+\delta) S E)\,dt - \tfrac12 d\langle E\rangle + \sigma\beta_0 S^2 I\, dW$; the stochastic integral has zero conditional mean, so the discretized expectation identity can be solved for the value of $\beta_0$ at an intermediate time, giving $\widehat\beta$. Dividing the summed squared increments of $E$ by the integrated $\beta_0^2 S^2 I^2$ estimates the quadratic-variation coefficient, which is the square of the noise intensity (the source labels this estimate $\sigma^*$). Unobserved compartments are reconstructed from incidence data by discretizing the deterministic equations, and an implicit Euler scheme keeps simulated states nonnegative.

## Sources

- A. Mummert and O. M. Otunuga, "Parameter identification for a stochastic SEIRS epidemic model: case study influenza", Journal of Mathematical Biology 79 (2019), 705–729, Eqs. (1)–(3), Theorem 1 and Eqs. (6)–(14), <https://doi.org/10.1007/s00285-019-01374-z> (PMCID: PMC7080032).

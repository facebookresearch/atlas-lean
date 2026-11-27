# Sharp extinction–persistence threshold for the switching stochastic SIQRS model

**Model.** Susceptible $S$, infected $I$, quarantined $Q$ and recovered $R$ hosts, with recovered hosts losing immunity, live in an environment $r(t)$ given by an irreducible continuous-time Markov chain on $\mathcal M = \{1,\dots,m_0\}$ with stationary law $\pi$, independent of Brownian motions $W_1,\dots,W_4$:

$$\begin{aligned}
dS &= \big[A(r) - F(S,I,r)I - \mu(r)S + \gamma_5(r)R\big]dt + \sigma_1(r)S\,dW_1,\\
dI &= \big[F(S,I,r) - \mu(r) - \gamma_1(r) - \gamma_2(r)\big]I\,dt + \sigma_2(r)I\,dW_2,\\
dQ &= \big[\gamma_2(r)I - (\mu(r) + \gamma_3(r) + \gamma_4(r))Q\big]dt + \sigma_3(r)Q\,dW_3,\\
dR &= \big[\gamma_3(r)Q - (\mu(r) + \gamma_5(r))R\big]dt + \sigma_4(r)R\,dW_4,
\end{aligned}$$

with $\sigma_i \ne 0$. Here $A$ is recruitment, $\mu$ natural death, $\gamma_1$ disease death, $\gamma_2$ quarantine, $\gamma_3$ recovery, $\gamma_4$ death in quarantine, $\gamma_5$ loss of immunity, and $F(S,I,k)$ a general per-infective incidence function (bilinear, saturated, Beddington–DeAngelis and similar forms are allowed). Let $c_2(k) = \mu(k) + \gamma_1(k) + \gamma_2(k)$.

**Threshold.** Without infection the pair $(S, r)$ has a unique invariant probability measure $\nu_0$ on $(0,\infty)\times\mathcal M$. Define the invasion rate of the disease

$$\lambda = \sum_{k\in\mathcal M}\int_{(0,\infty)}\Big[F(s,0,k) - c_2(k) - \frac{\sigma_2^2(k)}{2}\Big]\nu_0(ds,\{k\}).$$

Without switching and with $F(s,i) = \beta s$, $\lambda = \beta A/\mu - c_2 - \sigma_2^2/2$.

**Theorem.**
1. *Well-posedness.* From every initial value in $\mathbb R^4_+\times\mathcal M$ there is a unique global solution that stays in $\mathbb R^4_+$; the disease-free boundary $\{I = 0\}$ is invariant.
2. *Extinction.* If $\lambda < 0$, then from every interior initial condition, almost surely $\lim_{t\to\infty}\frac{\ln I(t)}{t} = \lambda$, $\limsup\frac{\ln Q(t)}{t} < 0$, $\limsup\frac{\ln R(t)}{t} < 0$, and the occupation measures of $(S,I,Q,R,r)$ converge weakly to $\nu_0$ (concentrated on $I = Q = R = 0$).
3. *Persistence.* If $\lambda > 0$, then $(S,I,Q,R,r)$ has a unique invariant probability measure $\mu^*$ on $(0,\infty)^4\times\mathcal M$, and transition probabilities converge to it exponentially fast in total variation: $\lim_{t\to\infty}e^{\rho t}\|P(t,j,\cdot) - \mu^*\| = 0$ for some $\rho > 0$.

Apart from the critical case $\lambda = 0$, this classifies the dynamics completely.

## Proof sketch

$\lambda$ is the Lyapunov exponent of $I$ when it is rare: by Itô's formula $d\ln I = [F(S,I,r) - c_2(r) - \sigma_2^2(r)/2]dt + \sigma_2\,dW_2$, and when $I$ is small, $(S,r)$ is close to the disease-free process, whose ergodic averages are governed by $\nu_0$. For $\lambda < 0$, ergodicity of the boundary process and the strong law for the martingale term give $\frac1t\ln I \to \lambda$; $Q$ and $R$ are then driven by an exponentially vanishing input. For $\lambda > 0$, the boundary is repelling on average, which yields a Foster–Lyapunov drift condition for a function penalizing both large populations and small $I$; together with the non-degeneracy $\sigma_i \ne 0$ and irreducibility of the switching, this gives a unique invariant measure and exponential ergodicity (in the framework of stochastic persistence for Kolmogorov systems of Hening and Nguyen).

## Sources

- Alexandru Hening, Dang H. Nguyen, Trang Ta and Sergiu C. Ungureanu, "Long-term behavior of stochastic SIQRS epidemic models", *Journal of Mathematical Biology* 90 (2025), 41, <https://doi.org/10.1007/s00285-025-02204-1>. Preprint version: arXiv:2406.01718 (2024), switching SIQRS model, definition of the threshold $\lambda$ and its remarks, well-posedness, extinction and persistence theorems, <https://doi.org/10.48550/arXiv.2406.01718>.

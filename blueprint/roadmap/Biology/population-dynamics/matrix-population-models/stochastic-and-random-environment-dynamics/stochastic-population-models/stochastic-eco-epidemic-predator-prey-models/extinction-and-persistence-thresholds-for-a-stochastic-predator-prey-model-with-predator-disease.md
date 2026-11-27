# Extinction and persistence thresholds for a stochastic predator–prey model with disease in the predator

**Model.** Let $x$ be the prey density and $S$, $I$ the susceptible and infected generalist-predator densities. With independent Brownian motions $W_1, W_2, W_3$ and positive constants,

$$\begin{aligned}
dx &= \Big[x(a_1 - b_1 x) - \frac{a x (S+I)}{b + S + I + x}\Big]dt + \sigma_1 x\, dW_1,\\
dS &= \Big[S\Big(a_2 - \Big(\frac{1}{c + x} + h\Big)(S+I)\Big) - \beta(S,I) S I + \gamma I\Big]dt + \sigma_2 S\, dW_2,\\
dI &= \big[\beta(S,I) S I - \alpha I\big]dt + \sigma_3 I\, dW_3,
\end{aligned}$$

with standard incidence $\beta(S,I) = \beta^*/(S + I + k)$. The predator carrying capacity $a_2/(1/(c+x) + h)$ lies between $a_2 c/(1 + hc)$ and $a_2/h$, and recovered predators return to $S$ ($\gamma$ = recovery rate, $\alpha$ = removal rate of infected predators). Note $\beta(S,I)S \le \beta^*$ and $\beta(S,I) I \le \beta^*$.

**Theorem.** For every initial value in $\overline{\mathbb{R}}_+^3$ there is a unique global solution staying in $\overline{\mathbb{R}}_+^3$ (in $\mathbb{R}_+^3$ if the initial value is positive), and $\sup_t \mathbb{E}\,x(t)^\theta < \infty$ for all $\theta \ge 1$. Moreover, for initial values with $x(0) > 0$ and $S(0) + I(0) > 0$ (on the boundary faces $x \equiv 0$ or $S \equiv I \equiv 0$ the corresponding species stays absent):
1. *Predator decline.* If $\max\{\beta^* - \alpha,\ a_2\} < \dfrac{1}{2\left(\sigma_2^{-2} + \sigma_3^{-2}\right)}$, then $S(t) \to 0$ and $I(t) \to 0$ a.s.
2. *Prey decline.* If $a_1 - \tfrac12\sigma_1^2 < 0$, then $x(t) \to 0$ a.s.
3. *Disease-free sustainability.* If

$$a_1 - a - \tfrac12\sigma_1^2 > 0, \qquad a_2 - \beta^* - \tfrac12\sigma_2^2 > 0, \qquad \beta^* - \alpha - \tfrac12\sigma_3^2 < 0,$$

then $I(t) \to 0$ a.s. and there is $\varepsilon > 0$, independent of the initial value, with $\liminf_{t\to\infty}\frac1t\int_0^t x\,ds > \varepsilon$ and $\liminf_{t\to\infty}\frac1t\int_0^t S\,ds > \varepsilon$ a.s.
4. *Invariant measure.* Under the conditions of item 3 and $\alpha > \beta^*$, the transition semigroup has a Borel invariant measure on $\overline{\mathbb{R}}_+^3$.

## Proof sketch

Itô's formula for $\log I$ together with $\beta(S,I)S \le \beta^*$ gives $\log I(t) \le \log I(0) + (\beta^* - \alpha - \tfrac12\sigma_3^2)t + \sigma_3 W_3(t)$, so the infection dies out once the noise-corrected growth rate is negative; the strong law for Brownian motion removes the martingale term. For prey and susceptible predators, lower bounds of the form $\log X(t) \ge \lambda t - \mu\int_0^t X\,ds + \text{martingale}$ yield positive time-averages (persistence in mean), with $a_1 - a$ and $a_2 - \beta^*$ the worst-case per-capita growth rates after predation and infection losses. Combining the mean-persistence bounds with a Lyapunov-type recurrence argument for the semigroup produces the invariant measure.

## Sources

- Yujie Gao, Malay Banerjee and Ton Viet Ta, "Dynamics of infectious diseases in predator–prey populations: A stochastic model, sustainability, and invariant measure", *Mathematics and Computers in Simulation* 227 (2025), 103–120, <https://doi.org/10.1016/j.matcom.2024.07.031>. Preprint version: arXiv:2306.08752 (2023), Sections 2–5 (global solutions, decline of species, sustainability, Borel invariant measure), <https://doi.org/10.48550/arXiv.2306.08752>.

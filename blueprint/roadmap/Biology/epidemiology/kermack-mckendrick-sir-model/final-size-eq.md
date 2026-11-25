# Final-size equation (Kermack–McKendrick 1927)

Let $(S, I, R)$ be a [solution of the SIR system](is-solution.md) with transmission rate $\beta$, removal rate $\gamma$ and population size $N$, with $\gamma \ne 0$, $S(0) + I(0) + R(0) = N$ and $R(0) = 0$. If
$S(t) \to S_\infty$ and $I(t) \to 0$ as $t \to \infty$, then

$$S_\infty = S(0) \exp\left(-\frac{R_0 (N - S_\infty)}{N}\right), \qquad R_0 = \frac{\beta}{\gamma},$$

where the quotient by $N$ is read as $0$ when $N = 0$.

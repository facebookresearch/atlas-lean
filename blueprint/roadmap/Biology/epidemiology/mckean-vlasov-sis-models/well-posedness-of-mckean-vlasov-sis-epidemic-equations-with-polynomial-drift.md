# Well-posedness of McKean–Vlasov SIS epidemic equations with polynomial drift

**Equation.** Let $N(t) > 0$ be a locally absolutely continuous population size and $W$ a $d$-dimensional Brownian motion. The number of infected individuals $I_t \in [0, N(t)]$ solves the McKean–Vlasov SDE

$$dI_t = \sum_{i=0}^k b_i\bigl(t, N(t), \mathcal L(I_t)\bigr) I_t^i\,dt + f\bigl(t, I_t, N(t) - I_t\bigr)\,dW_t, \qquad I_0 = \xi_0 \in [0, N(0)],$$

whose drift is polynomial in $I_t$ with coefficients depending on the law $\mathcal L(I_t)$. It contains, for example,

$$dI_t = \Bigl[\Bigl(\beta_0\mathbb E[I_t] + \bigl(\beta + \beta_1\tfrac{\mathbb E[I_t]}{N}\bigr) I_t\Bigr)(N - I_t) - (\mu + \gamma) I_t\Bigr]dt + I_t\, g\,(N - I_t)^{\eta}\,dW_t + \cdots,$$

where infection pressure depends on the mean prevalence, and the classical stochastic SIS models with environmental noise in the transmission rate are special cases.

**Theorem.** Assume, for $p = 1$:
- (C.1) each $b_i$ is bounded above by a locally integrable $\hat b_i(\cdot, N)$, is Lipschitz in the measure argument with respect to a metric $\vartheta$ on distributions with locally integrable constant, and is bounded on bounded sets (together with a one-sided growth bound on the drift);
- (C.2) $f$ is $\tfrac12$-Hölder on compacts: $|f(s,x,y) - f(s,\tilde x,\tilde y)| \le \lambda_n(s)(|x - \tilde x|^{1/2} + |y - \tilde y|^{1/2})$ on $[0, n]^2$;
- (C.3) $b_0(\cdot, N, \nu) \ge 0$, $\dot N \ge \sum_i b_i(\cdot, N, \nu) N^i$ for all $\nu$, and $f(\cdot, 0, y) = f(\cdot, x, 0) = 0$.

Then pathwise uniqueness holds, with the stability estimate $\mathbb E|I_t - \tilde I_t| \le e^{\int_0^t (\hat b_{k+1} + \hat\lambda_{k+1})(s, N(s))\,ds}\,\mathbb E|I_0 - \tilde I_0|$, where $\hat b_{k+1}, \hat\lambda_{k+1}$ are the one-sided growth and measure-Lipschitz rates of the whole drift, and there is a unique strong solution with $0 \le I \le N$ and an exponential first-moment growth bound. An $L^p$ version ($p \ge 2$) holds under a Lipschitz condition on $f$. Under a linear growth bound $|f(s, x, y)| \le l_n(s) x$, sufficient conditions on the time-averaged coefficients give almost sure extinction $I_t \to 0$, and complementary conditions give persistence.

## Expansion

The proof applies general pathwise-uniqueness and strong-existence results for McKean–Vlasov SDEs: the one-sided bound on the polynomial drift and the Lipschitz dependence on the law give the first-moment comparison estimate, while the $\tfrac12$-Hölder diffusion is handled by a Yamada–Watanabe-type argument, which is exactly the regularity of $\sqrt{I(N - I)}$-type noise. Condition (C.3) makes $0$ and $N$ barriers: no new infections from zero prevalence beyond the external term $b_0 \ge 0$, and the drift at $I = N$ cannot exceed the population growth, so solutions stay in $[0, N]$. Extinction results apply Itô's formula to $\log I_t$ and a strong law for continuous martingales.

## Sources

- A. Kalinin, T. Meyer-Brandis and A. Steibel, "On McKean-Vlasov SDEs with polynomial drifts for SIS epidemic models", arXiv:2604.19308 (2026), Propositions 2.3, 2.6, 2.10, 2.12 and 3.5, <https://doi.org/10.48550/arXiv.2604.19308>.

# Long-time behavior of the reduced heterogeneous SIR model

Consider the [reduced heterogeneous SIR model](gaussian-self-similar-sir-reduction.md) normalized to $N = 1$, with constants $\mu_0 \ge 0$, $D \ge 0$, $\beta_1 > 0$, $\gamma > 0$, initial values $S(0) = S^0 > 0$, $I(0) = I_0 > 0$, $R(0) = 0$, $S^0 + I_0 = 1$, $\bar\beta(0) \ge \beta_0$, and average transmission rate $\bar\beta = \beta_0 + \beta_1\lambda^2$.

**Statement.**

1. $\bar\beta(t) \ge \beta_0$ for all $t \ge 0$, and $(S, I, R) \to (S^\infty, 0, R^\infty)$ with $S^\infty \in [0, 1)$, $R^\infty \in (0, 1]$ and $S^\infty + R^\infty = 1$.
2. If $\mu_0 > 0$, then $\bar\beta(t)$ stays bounded and converges to

$$\bar\beta^\infty = \beta_0 + \frac{D\beta_1}{\mu_0},$$

and the limits satisfy $\bar\beta^\infty S^\infty \le \gamma$.
3. If $\mu_0 = 0$ and $D > 0$, then $\bar\beta(t) \to +\infty$, $S^\infty = 0$ and $R^\infty = 1$: everybody is eventually infected.
4. If $\mu_0 > 0$ and $D = 0$, then $\bar\beta$ is nonincreasing and converges to $\beta_0$; if moreover $\bar\beta(0)S^0 > \gamma$, then $I$ has a unique maximum, and

$$S_\infty^{\mathrm{SIR}, \bar\beta(0)} \le S^\infty \le S_\infty^{\mathrm{SIR}, \beta_0},$$

where $S_\infty^{\mathrm{SIR}, \alpha}$ is the final susceptible fraction of the homogeneous SIR model with constant transmission rate $\alpha$ and the same $\gamma$, $S^0$, $I_0$.

Social diffusion therefore makes the transmission rate eventually increase again toward an equilibrium above $\beta_0$, while without it the heterogeneous epidemic is bracketed by two homogeneous SIR epidemics.

## Depends on

- [Gaussian self-similar reduction of the heterogeneous SIR model](gaussian-self-similar-sir-reduction.md)
- [Final size of the SIR epidemic](../../../kermack-mckendrick-sir-model/final-size-eq.md)

## Expansion

From the $\bar\beta$ equation, $\dot{\bar\beta} \le -2\mu_0(\bar\beta - \beta_0) + 2D\beta_1$, so $\bar\beta$ is bounded when $\mu_0 > 0$; the variation-of-constants formula $\bar\beta(t) - \bar\beta^\infty = (\bar\beta(0) - \bar\beta^\infty)e^{-2\mu_0 t} - \int_0^t 2(\bar\beta(s) - \beta_0)^2 I(s)e^{-2\mu_0(t-s)}ds$ and integrability of $I$ give convergence, and $\bar\beta^\infty S^\infty > \gamma$ would force $I$ to grow. When $\mu_0 = 0$, $\tau = 1/(\bar\beta - \beta_0)$ satisfies $\dot\tau = 2I - 2D\beta_1\tau^2$, which forces $\tau \to 0$. When $D = 0$, writing $S$ as a function of $R$, $S(R) = S^0\exp(-\gamma^{-1}\int_0^R\bar\beta)$, and $\beta_0 \le \bar\beta \le \bar\beta(0)$ give the bracketing through the classical final-size relation.

## Sources

- H. Berestycki, B. Desjardins, J. S. Weitz and J.-M. Oury, "Epidemic modeling with heterogeneity and social diffusion", Journal of Mathematical Biology 86 (2023), article 60, <https://doi.org/10.1007/s00285-022-01861-w> (PMC10039364), section 5.1, Propositions 1–5.

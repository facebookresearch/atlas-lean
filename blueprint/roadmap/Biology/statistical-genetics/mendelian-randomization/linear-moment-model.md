# Linear moment model for instrumental variables

Let $\mu$ be a measure on a measurable space $\Omega$. A linear moment model consists of real functions $Z$ (the instrument, in Mendelian randomization a genotype), $X$ (the exposure), $Y$ (the outcome) and $U$ (the residual) on $\Omega$ and real numbers $\alpha$ (intercept) and $\beta$ (coefficient) such that $Z$, $X$ and $U$ are square integrable with respect to $\mu$ and

$$Y(\omega) = \alpha + \beta X(\omega) + U(\omega) \qquad \text{for every } \omega \in \Omega.$$

The residual $U$ is arbitrary and may depend on $Z$, so the decomposition does not exclude a direct effect of the instrument on the outcome, and $\beta$ is only the coefficient of this decomposition, not a causal effect.

# Consistency of the time-dependent Cox estimator

For survival data with a scalar time-dependent covariate $z_i(t)$, let $\ell(b)$ be the time-dependent log partial likelihood, $U(b) = \sum_{i:\delta_i}(z_i(T_i) - \bar z_i(b))$ its score and $I(b) = \sum_{i:\delta_i}\mathrm{Var}_i(b)$ its information. Let $\hat\beta_n$ maximize the scalar time-dependent log partial likelihood whenever a maximizer exists. Suppose $U_n(\beta_0)/\sqrt n \Rightarrow Z$ and $I_n(b)/n \to i(b)$ uniformly in probability near $\beta_0$, with $i$ continuous at $\beta_0$ and $i(\beta_0) = v \ne 0$. Then $\hat\beta_n \to \beta_0$ in probability.

## Sources

- P. K. Andersen and R. D. Gill, "Cox's regression model for counting processes: a large sample study", Ann. Statist. 10 (1982), 1100–1120.

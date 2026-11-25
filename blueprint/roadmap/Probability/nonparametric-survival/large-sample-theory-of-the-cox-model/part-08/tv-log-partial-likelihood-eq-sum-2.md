# The scalar time-dependent log partial likelihood decomposes over events

For survival data with a scalar time-dependent covariate $z_i(t)$, let $\ell(b)$ be the time-dependent log partial likelihood, $U(b) = \sum_{i:\delta_i}(z_i(T_i) - \bar z_i(b))$ its score and $I(b) = \sum_{i:\delta_i}\mathrm{Var}_i(b)$ its information. Then $\ell$ is the sum over events $i$ of the scalar fixed-covariate log partial likelihoods of the single event $i$ with the covariate frozen at $T_i$.

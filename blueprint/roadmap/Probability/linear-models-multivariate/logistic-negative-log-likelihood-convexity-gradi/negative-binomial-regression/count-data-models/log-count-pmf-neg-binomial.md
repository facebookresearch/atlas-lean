# Negative binomial log-likelihood of one entry

Consider a count-matrix model for units $g$, samples $j$ and conditions $c$: each sample $j$ is a replicate of a condition $c(j)$ with exposure (size factor) $s_j \ge 0$, each unit $g$ has a valid count law $L_g$ (Poisson or negative binomial) and a rate $\lambda_{g,c} > 0$ in each condition, and the count $Y_{gj}$ has law $L_g$ at mean $\mu_{gj} = s_j\lambda_{g,c(j)}$. Write $\kappa_\theta(k, \eta) = k\eta - (k + \theta)\log(\theta + e^\eta)$ for the negative binomial log-likelihood kernel with shape $\theta$ (the part depending on the linear predictor $\eta$). If $L_g$ is negative binomial with shape $\theta$ and $s_j > 0$, then

$$\log P(Y_{gj} = k) = \log\frac{\theta^{(k)}}{k!} + \theta\log\theta + \kappa_\theta\big(k, \log\lambda_{g,c(j)} + \log s_j\big),$$

where $\theta^{(k)} = \theta(\theta + 1)\cdots(\theta + k - 1)$.

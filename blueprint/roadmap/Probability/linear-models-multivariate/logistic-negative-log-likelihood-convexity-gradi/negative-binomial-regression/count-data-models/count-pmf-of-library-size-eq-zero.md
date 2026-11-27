# A sample with zero exposure has zero counts

Consider a count-matrix model for units $g$, samples $j$ and conditions $c$: each sample $j$ is a replicate of a condition $c(j)$ with exposure (size factor) $s_j \ge 0$, each unit $g$ has a valid count law $L_g$ (Poisson or negative binomial) and a rate $\lambda_{g,c} > 0$ in each condition, and the count $Y_{gj}$ has law $L_g$ at mean $\mu_{gj} = s_j\lambda_{g,c(j)}$. If $s_j = 0$, then $P(Y_{gj} = k) = 1$ for $k = 0$ and $0$ otherwise, whatever the rates.

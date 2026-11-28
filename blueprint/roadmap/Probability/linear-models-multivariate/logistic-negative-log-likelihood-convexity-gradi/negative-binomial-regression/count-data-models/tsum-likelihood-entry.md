# Entry marginals of the count-matrix likelihood, sum form

Consider a valid count-matrix model with finitely many units and samples for units $g$, samples $j$ and conditions $c$: each sample $j$ is a replicate of a condition $c(j)$ with exposure (size factor) $s_j \ge 0$, each unit $g$ has a valid count law $L_g$ (Poisson or negative binomial) and a rate $\lambda_{g,c} > 0$ in each condition, and the count $Y_{gj}$ has law $L_g$ at mean $\mu_{gj} = s_j\lambda_{g,c(j)}$. Then for every $g, j, k$, $\sum_{Y : Y_{gj} = k}\prod_{g'}\prod_{j'}P(Y_{g'j'}) = P(Y_{gj} = k)$.

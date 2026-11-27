# Mean–variance relation of an entry of a count-matrix model

Consider a count-matrix model for units $g$, samples $j$ and conditions $c$: each sample $j$ is a replicate of a condition $c(j)$ with exposure (size factor) $s_j \ge 0$, each unit $g$ has a valid count law $L_g$ (Poisson or negative binomial) and a rate $\lambda_{g,c} > 0$ in each condition, and the count $Y_{gj}$ has law $L_g$ at mean $\mu_{gj} = s_j\lambda_{g,c(j)}$. Then for every $g$ and $j$, $\operatorname{Var}(Y_{gj}) = \mu_{gj} + \alpha_g\mu_{gj}^2$, with $\alpha_g$ the dispersion of $L_g$.

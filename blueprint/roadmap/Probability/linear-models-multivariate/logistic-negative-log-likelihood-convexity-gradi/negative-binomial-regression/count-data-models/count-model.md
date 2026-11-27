# Count-matrix model with exposures

A count-matrix model for units $g$, samples $j$ and conditions $c$ assigns to each sample a condition $c(j)$ and an exposure (size factor) $s_j$, and to each unit a count law $L_g$ (Poisson or negative binomial) and rates $\lambda_{g,c}$; the count of unit $g$ in sample $j$ has law $L_g$ at mean $s_j\lambda_{g,c(j)}$.

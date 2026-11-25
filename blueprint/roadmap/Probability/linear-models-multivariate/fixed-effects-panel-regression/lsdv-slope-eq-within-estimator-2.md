# The dummy-variable slope is the within estimator

Let $g : \iota \to G$ assign the observations of a finite set $\iota$ to finitely many groups, with group means $\bar y_h$. Let $D$ be the group-dummy matrix ($D_{ih} = 1$ if $g(i) = h$, else $0$), $X$ a real $\iota \times \pi$ regressor matrix, $y \in \mathbb{R}^\iota$, and $\ddot y_i = y_i - \bar y_{g(i)}$, $\ddot X_{ij} = X_{ij} - \bar X_{g(i), j}$ the within transformations. If $(\alpha, \beta)$ solves the normal equations of the dummy-variable regression and $\ddot X^\top\ddot X$ is invertible, then $\beta = (\ddot X^\top\ddot X)^{-1}\ddot X^\top\ddot y$.

## Sources

- J. M. Wooldridge, *Econometric Analysis of Cross Section and Panel Data*, 2nd ed., MIT Press (2010), §10.5.

# Residuals sum to zero at a normal-equation solution with an intercept

Let $X$ be a real $m \times \iota$ design matrix with a finite column index type $\iota$, $y \in \mathbb{R}^m$ and $\theta \in \mathbb{R}^\iota$. If $\theta$ solves the normal equations

$$X^{\mathsf T} X \theta = X^{\mathsf T} y$$

and $X$ has an intercept column $j$ ($X_{kj} = 1$ for every row $k$), then the residuals sum to zero:

$$\sum_{k} (y - X\theta)_k = 0 .$$

No rank condition on $X$ is needed.

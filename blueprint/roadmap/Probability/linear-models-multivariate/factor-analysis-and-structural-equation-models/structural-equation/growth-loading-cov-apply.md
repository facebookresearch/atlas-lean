# Covariance of the three-point linear growth model

Let $\Lambda$ be the $3 \times 2$ linear growth loading matrix with rows $(1, 0), (1, 1), (1, 2)$, $G$ a symmetric $2 \times 2$ matrix (random intercept and slope covariance) and $\theta \in \mathbb{R}^3$ (error variances), and let $\Sigma = \Lambda G\Lambda^\top + \operatorname{diag}(\theta)$. Then for $s, t \in \{0, 1, 2\}$, $\Sigma_{st} = G_{00} + (s + t)G_{01} + st\,G_{11} + \theta_s\mathbf 1[s = t]$.

## Sources

- T. E. Duncan and S. C. Duncan, "The ABC's of LGM: an introductory guide to latent variable growth curve modeling", *Social and Personality Psychology Compass* 3 (2009): Figure 2.

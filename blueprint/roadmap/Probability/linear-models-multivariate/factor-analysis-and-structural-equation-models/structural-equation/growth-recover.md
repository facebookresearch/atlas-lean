# Recovering linear growth parameters from the covariance

Let $\Lambda$ be the $3 \times 2$ linear growth loading matrix with rows $(1, 0), (1, 1), (1, 2)$, $G$ a symmetric $2 \times 2$ matrix (random intercept and slope covariance) and $\theta \in \mathbb{R}^3$ (error variances), and let $\Sigma = \Lambda G\Lambda^\top + \operatorname{diag}(\theta)$. Then $G_{01} = \Sigma_{02} - \Sigma_{01}$, $G_{00} = 2\Sigma_{01} - \Sigma_{02}$, $G_{11} = (\Sigma_{12} + \Sigma_{01} - 2\Sigma_{02})/2$, $\theta_0 = \Sigma_{00} - G_{00}$, $\theta_1 = \Sigma_{11} - (G_{00} + 2G_{01} + G_{11})$ and $\theta_2 = \Sigma_{22} - (G_{00} + 4G_{01} + 4G_{11})$.

## Sources

- T. E. Duncan and S. C. Duncan, "The ABC's of LGM: an introductory guide to latent variable growth curve modeling", *Social and Personality Psychology Compass* 3 (2009): Figure 2.

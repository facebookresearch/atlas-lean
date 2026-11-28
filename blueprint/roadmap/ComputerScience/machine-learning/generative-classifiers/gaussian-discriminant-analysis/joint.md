# Joint density of a class and features

Consider Gaussian discriminant analysis on $\mathbb{R}^\iota$, for a finite index set $\iota$, with a finite set of classes, prior weights $\pi_c$, class means $\mu_c$ and a shared real matrix $S$ in the role of the precision matrix. The joint score of class $c$ and features $x$ is $\pi_c\, g_S(x; \mu_c)$, where $g_S(x; \mu)$ is the Gaussian density formula with mean $\mu$ and $S^{-1}$ in place of the covariance. When $S$ is positive definite it is the joint density of the class and the features under the Gaussian model with covariance $S^{-1}$.

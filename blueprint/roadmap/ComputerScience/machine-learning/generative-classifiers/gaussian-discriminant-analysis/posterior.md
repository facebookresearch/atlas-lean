# Posterior score of a class

Consider Gaussian discriminant analysis on $\mathbb{R}^\iota$, for a finite index set $\iota$, with a finite set of classes $C$, prior weights $\pi_c$, class means $\mu_c$ and a shared real matrix $S$ in the role of the precision matrix. Write $j(c, x) = \pi_c\, g_S(x; \mu_c)$ for the joint score, where $g_S(x; \mu)$ is the Gaussian density formula with mean $\mu$ and $S^{-1}$ in place of the covariance. The posterior score of class $c$ at $x$ is the ratio

$$\frac{j(c, x)}{\sum_{c' \in C} j(c', x)},$$

with every score equal to $0$ when the denominator is $0$. For any $S$ this is only an algebraic ratio: a positive denominator does not make it a Gaussian posterior, since $S^{-1}$ need not be a covariance matrix (in dimension two, $S = -I$ can give a positive denominator). When $S$ is positive definite, $g_S(\cdot\,; \mu_c)$ is the Gaussian density with covariance $S^{-1}$, the denominator is positive, and the score is the posterior probability of class $c$ given $x$.

# Mean of the Dirichlet distribution

Let
$\alpha = (\alpha_0, \dots, \alpha_n) \in \mathbb{R}^{n+1}$ with $\alpha_j > 0$ for every $j$. For
every $i$, the $i$-th coordinate of a random vector $\theta$ with the Dirichlet distribution
$\mathrm{Dir}(\alpha)$ has mean

$$\mathbb{E}[\theta_i] = \frac{\alpha_i}{\sum_{j=0}^{n} \alpha_j}.$$

Formally the left side is the integral of $\max(\theta_i, 0)$ with respect to
$\mathrm{Dir}(\alpha)$; this is the mean of $\theta_i$ because $\theta_i > 0$ almost surely.

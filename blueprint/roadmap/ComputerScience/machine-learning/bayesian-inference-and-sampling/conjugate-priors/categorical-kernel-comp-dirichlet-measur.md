# Prior predictive of the Dirichlet–categorical model

Let $\alpha \in \mathbb{R}^{n+1}$
with $\alpha_i > 0$ for every $i$. Drawing a parameter $\theta$ from the Dirichlet
distribution $\mathrm{Dir}(\alpha)$ and then one label from the categorical likelihood with
parameter $\theta$ gives the label $i \in \{0, \dots, n\}$ with probability
$\alpha_i / \sum_j \alpha_j$, which is the mean of $\theta_i$ under $\mathrm{Dir}(\alpha)$.

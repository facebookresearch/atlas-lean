# Dirichlet–multinomial conjugacy

Let $\alpha = (\alpha_0, \dots, \alpha_n)$ have positive
real entries and let $k = (k_0, \dots, k_n)$ be natural numbers (counts). The measure with density
$\theta \mapsto \prod_{i=0}^{n} \max(\theta_i, 0)^{k_i}$ with respect to the Dirichlet distribution
$\mathrm{Dir}(\alpha)$, that is, $\mathrm{Dir}(\alpha)$ weighted by the likelihood of the counts
$k$, equals

$$\frac{B(\alpha + k)}{B(\alpha)} \, \mathrm{Dir}(\alpha + k),$$

where $B$ is the multivariate Beta function and $\alpha + k$ is taken entrywise.

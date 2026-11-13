# The evidence from a factorization of densities

Let $\nu$ be an s-finite measure on a
measurable space $\Theta$ and $\rho$ an s-finite measure on a measurable space $\mathcal{X}$. Let
$p : \Theta \to [0, \infty]$, $q : \Theta \times \mathcal{X} \to [0, \infty]$,
$c : \mathcal{X} \to [0, \infty]$ and $r : \mathcal{X} \times \Theta \to [0, \infty]$ be measurable
functions such that $\int r(x, \theta) \, d\nu(\theta) = 1$ for every $x \in \mathcal{X}$ and
$p(\theta) \, q(\theta, x) = c(x) \, r(x, \theta)$ for all $\theta \in \Theta$ and
$x \in \mathcal{X}$. If the prior $\mu$ is the measure on $\Theta$ with density $p$ with respect
to $\nu$, and the likelihood $\kappa$ is a kernel from $\Theta$ to $\mathcal{X}$ such that each
$\kappa(\theta)$ has density $q(\theta, \cdot)$ with respect to $\rho$, then the marginal law of
the data, the measure $\kappa \circ \mu$ on $\mathcal{X}$ given by
$(\kappa \circ \mu)(s) = \int \kappa(\theta)(s) \, d\mu(\theta)$ for measurable $s$, has density
$c$ with respect to $\rho$.

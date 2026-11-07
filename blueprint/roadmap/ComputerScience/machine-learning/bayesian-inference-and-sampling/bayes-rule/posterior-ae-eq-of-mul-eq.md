# Bayes' rule for densities

Let $\Theta$ be a nonempty standard Borel space, $\nu$ an
s-finite measure on $\Theta$ and $\rho$ an s-finite measure on a measurable space $\mathcal{X}$.
Let $p : \Theta \to [0, \infty]$, $q : \Theta \times \mathcal{X} \to [0, \infty]$,
$c : \mathcal{X} \to [0, \infty]$ and $r : \mathcal{X} \times \Theta \to [0, \infty]$ be measurable
functions such that $\int r(x, \theta) \, d\nu(\theta) = 1$ for every $x \in \mathcal{X}$ and
$p(\theta) \, q(\theta, x) = c(x) \, r(x, \theta)$ for all $\theta \in \Theta$ and
$x \in \mathcal{X}$. Let the prior $\mu$ be a finite measure on $\Theta$ with density $p$ with
respect to $\nu$, and let the likelihood $\kappa$ be a Markov kernel from $\Theta$ to
$\mathcal{X}$ such that each $\kappa(\theta)$ has density $q(\theta, \cdot)$ with respect to
$\rho$. Then for almost every $x$ with respect to the marginal law of the data
$\kappa \circ \mu$, given by $(\kappa \circ \mu)(s) = \int \kappa(\theta)(s) \, d\mu(\theta)$, the
posterior $\kappa^\dagger_\mu(x)$ of $\kappa$ with respect to $\mu$ is the measure with density
$r(x, \cdot)$ with respect to $\nu$.

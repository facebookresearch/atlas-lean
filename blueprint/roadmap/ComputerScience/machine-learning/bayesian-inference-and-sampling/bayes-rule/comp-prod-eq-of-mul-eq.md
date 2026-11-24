# Disintegration of the joint law from a factorization of densities

Let $\nu$ be an
s-finite measure on a measurable space $\Theta$ and $\rho$ an s-finite measure on a measurable
space $\mathcal{X}$. Let $p : \Theta \to [0, \infty]$,
$q : \Theta \times \mathcal{X} \to [0, \infty]$, $c : \mathcal{X} \to [0, \infty]$ and
$r : \mathcal{X} \times \Theta \to [0, \infty]$ be measurable functions such that
$\int r(x, \theta) \, d\nu(\theta) = 1$ for every $x \in \mathcal{X}$ and
$p(\theta) \, q(\theta, x) = c(x) \, r(x, \theta)$ for all $\theta \in \Theta$ and
$x \in \mathcal{X}$. Let the prior $\mu$ be an s-finite measure on $\Theta$ with density $p$ with
respect to $\nu$, let the likelihood $\kappa$ be an s-finite kernel from $\Theta$ to $\mathcal{X}$
such that each $\kappa(\theta)$ has density $q(\theta, \cdot)$ with respect to $\rho$, and let
$\eta$ be an s-finite kernel from $\mathcal{X}$ to $\Theta$ such that each $\eta(x)$ has density
$r(x, \cdot)$ with respect to $\nu$. Write $\kappa \circ \mu$ for the marginal law of the data,
$(\kappa \circ \mu)(s) = \int \kappa(\theta)(s) \, d\mu(\theta)$, and $\mu \otimes \kappa$ for the
joint law on $\Theta \times \mathcal{X}$,
$(\mu \otimes \kappa)(t) = \int \kappa(\theta)(\{x : (\theta, x) \in t\}) \, d\mu(\theta)$, and
similarly $(\kappa \circ \mu) \otimes \eta$ on $\mathcal{X} \times \Theta$. Then
$(\kappa \circ \mu) \otimes \eta$ is the image of $\mu \otimes \kappa$ under the swap
$(\theta, x) \mapsto (x, \theta)$.

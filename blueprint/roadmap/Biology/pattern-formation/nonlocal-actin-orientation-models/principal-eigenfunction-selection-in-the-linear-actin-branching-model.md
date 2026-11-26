# Principal-eigenfunction selection in the linear actin branching model

Let $u(\theta, t) \ge 0$ be the density of actin filaments with orientation $\theta \in S^1$ at a lamellipodial leading edge. In the first-order branching model (generalizing Maly and Borisy),

$$
\partial_t u(\theta,t) = \lambda\,(\mathcal{B} \star u)(\theta,t) - \kappa(\theta)\,u(\theta,t),
$$

where $(\mathcal{B} \star u)(\theta) = \int_{S^1} \mathcal{B}(\theta - \omega)\,u(\omega)\,d\omega$ is branching by a real, positive, symmetric $C^2$ kernel with $\|\mathcal{B}\|_1 = 1$, $\lambda > 0$ is the branching rate, and $\kappa$ is a real, strictly positive, symmetric $C^2$ capping rate.

**Theorem.** The operator $\mathcal{A} u = \lambda\,\mathcal{B} \star u - \kappa u$ has an isolated, algebraically simple principal eigenvalue with a positive eigenfunction. Consequently, for given $\mathcal{B}$ and $\kappa$ there is exactly one branching rate $\lambda$ for which the equation has a stable non-trivial equilibrium, and solutions with positive initial data align asymptotically with the principal eigenfunction: the model selects a unique orientation pattern.

## Expansion

$\mathcal{A}$ is resolvent positive; outside the segment $[-\sup\kappa, -\inf\kappa]$ its spectrum consists of eigenvalues because $u \mapsto \mathcal{B} \star u$ is compact, and some power of the resolvent-type operator $\mathcal{B} \star (\gamma + \kappa)^{-1}$ is strongly positive. The Krein–Rutman theorem then gives a simple principal eigenvalue with positive eigenfunction, which dominates the long-time dynamics. A non-trivial equilibrium requires the principal eigenvalue to vanish, which pins down $\lambda$ uniquely since the principal eigenvalue increases strictly with $\lambda$.

## Sources

- Daniel Smith and Jian Liu, *Nonlocal actin orientation models select for a unique orientation pattern*, arXiv:1301.6137, Section 2 ("First-order Branching"), principal-eigenvalue theorem and the proposition on the unique branching rate. <https://doi.org/10.48550/arXiv.1301.6137>

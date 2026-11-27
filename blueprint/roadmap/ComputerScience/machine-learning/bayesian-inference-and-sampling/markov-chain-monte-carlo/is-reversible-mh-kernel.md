# The Metropolis–Hastings kernel is reversible

Let $\alpha$ be a finite state space with a
measurable structure in which singletons are measurable, $\pi$ a probability distribution on
$\alpha$ and $Q$ a proposal assigning to each $x \in \alpha$ a probability distribution
$Q(x, \cdot)$ on $\alpha$. Then the Markov kernel $\kappa$ of the Metropolis–Hastings step for
target $\pi$ and proposal $Q$ is reversible with respect to $\pi$, viewed as a measure: for all
measurable sets $A$ and $B$, $\int_A \kappa(x, B) \, d\pi(x) = \int_B \kappa(x, A) \, d\pi(x)$.

# The target is stationary for Metropolis–Hastings

Let $\alpha$ be a finite state space
with a measurable structure in which singletons are measurable, $\pi$ a probability distribution
on $\alpha$ and $Q$ a proposal assigning to each $x \in \alpha$ a probability distribution
$Q(x, \cdot)$ on $\alpha$. Then $\pi$, viewed as a measure, is invariant for the Markov kernel
$\kappa$ of the Metropolis–Hastings step for target $\pi$ and proposal $Q$: for every measurable
set $B$, $\int \kappa(x, B) \, d\pi(x) = \pi(B)$.

No positivity or symmetry assumption on $\pi$ or $Q$ is needed.

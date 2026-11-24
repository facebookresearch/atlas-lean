# Detailed balance for Metropolis–Hastings

Let $\pi$ be a probability distribution on a
type $\alpha$, $Q$ a proposal assigning to each $x \in \alpha$ a probability distribution
$Q(x, \cdot)$ on $\alpha$, and $P(x, y)$ the probability that one Metropolis–Hastings step for
target $\pi$ and proposal $Q$ moves from $x$ to $y$. Then $\pi(x) P(x, y) = \pi(y) P(y, x)$ for
all $x, y \in \alpha$.

For $x \ne y$ both sides equal $\min(\pi(x) Q(x, y), \pi(y) Q(y, x))$; no positivity or symmetry
assumption on $\pi$ or $Q$ is needed.

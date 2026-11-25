# Metropolis–Hastings step

For a probability distribution $\pi$ on $\alpha$ (the target)
and a proposal $Q$ assigning to each $x \in \alpha$ a probability distribution $Q(x, \cdot)$ on
$\alpha$, one Metropolis–Hastings step from $x$ is the distribution of the following move: draw
$y$ from $Q(x, \cdot)$, then move to $y$ with the Metropolis–Hastings acceptance probability
$a(x, y)$, and otherwise stay at $x$.

# Metropolis–Hastings transition matrix

For a finite set $\alpha$, a probability distribution $\pi$ on $\alpha$ (the target) and a
proposal $Q$ assigning to each $x \in \alpha$ a probability distribution $Q(x, \cdot)$, the
transition matrix of the Metropolis–Hastings chain is the real $\alpha \times \alpha$ matrix whose
entry $P(x, y)$ is the probability that one [Metropolis–Hastings step](mh-step.md) for $\pi$ and
$Q$ moves from $x$ to $y$.

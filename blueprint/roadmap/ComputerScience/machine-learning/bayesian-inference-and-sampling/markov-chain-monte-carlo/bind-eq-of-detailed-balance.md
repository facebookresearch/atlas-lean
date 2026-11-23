# Detailed balance gives a stationary distribution

Let $\alpha$ be a finite set, $\pi$ a
probability distribution on $\alpha$ and $P$ a transition rule assigning to each $x \in \alpha$ a
probability distribution $P(x, \cdot)$ on $\alpha$. If $\pi(x) P(x, y) = \pi(y) P(y, x)$ for all
$x, y \in \alpha$, then one step of $P$ started from $\pi$ is again distributed as $\pi$: for every
$y \in \alpha$, $\sum_{x \in \alpha} \pi(x) P(x, y) = \pi(y)$.

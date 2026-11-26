# Log-likelihood of an exponential random graph model as a log probability

Let $V$ be a finite vertex set, $t$ a statistic assigning to each simple graph $G$ on $V$ a vector $t(G) \in \mathbb{R}^\iota$ over a finite index set $\iota$, and $\theta \in \mathbb{R}^\iota$. The log-likelihood $\ell(\theta; y) = \langle\theta, t(y)\rangle - \log \kappa(\theta)$ of a graph $y$, with $\kappa(\theta) = \sum_H e^{\langle\theta, t(H)\rangle}$, equals $\log P_\theta(y)$, where $P_\theta(y) = e^{\langle\theta, t(y)\rangle}/\kappa(\theta)$ is the exponential random graph probability of $y$.

# Glauber dynamics for the antiferromagnetic Ising model

Let $G$ be a simple graph on $\{1, \dots, n\}$, $\beta \in \mathbb{R}$, and let $w_\beta(\sigma) = \exp\big(-\beta \sum_{\{u,v\} \in E(G)} \sigma_u \sigma_v\big)$ be the antiferromagnetic Ising weight on spin configurations $\sigma \in \{+1, -1\}^n$. The Glauber (heat-bath) dynamics picks a uniform vertex $v$ and resamples the spin at $v$ from the Gibbs distribution conditioned on the other spins. Its transition matrix is

$$P(\sigma, \tau) = \frac{1}{n} \sum_{v = 1}^{n} \mathbf{1}[\tau_u = \sigma_u \text{ for all } u \ne v]\, \frac{w_\beta(\tau)}{w_\beta(\tau) + w_\beta(\tau^{(v)})},$$

where $\tau^{(v)}$ is $\tau$ with the spin at $v$ flipped. For $n = 0$ the factor $1/n$ is read as $0$.

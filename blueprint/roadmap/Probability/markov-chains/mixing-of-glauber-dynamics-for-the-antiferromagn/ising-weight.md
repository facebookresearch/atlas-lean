# Antiferromagnetic Ising weight

Let $G$ be a simple graph on the vertex set $\{1, \dots, n\}$ with edge set $E$, let $\beta \in \mathbb{R}$, and let $\sigma$ be a spin configuration, where each vertex $u$ carries the spin $\sigma_u \in \{+1, -1\}$. The Gibbs weight of $\sigma$ in the zero-field antiferromagnetic Ising model (coupling $J = -1$) at inverse temperature $\beta$ is

$$w_\beta(\sigma) = \exp\Big(-\beta \sum_{\{u, v\} \in E} \sigma_u \sigma_v\Big),$$

with each edge counted once. Equivalently the exponent is $-\beta \cdot \tfrac12 \sum_{u} \sum_{v \sim u} \sigma_u \sigma_v$.

# Gibbs distribution of the antiferromagnetic Ising model

Let $G$ be a simple graph on $\{1, \dots, n\}$ and $\beta \in \mathbb{R}$. The Gibbs distribution of the zero-field antiferromagnetic Ising model on $G$ at inverse temperature $\beta$ assigns to a spin configuration $\sigma \in \{+1, -1\}^n$ the probability

$$\mu_\beta(\sigma) = \frac{w_\beta(\sigma)}{\sum_{\tau \in \{+1,-1\}^n} w_\beta(\tau)}, \qquad w_\beta(\sigma) = \exp\Big(-\beta \sum_{\{u, v\} \in E(G)} \sigma_u \sigma_v\Big).$$

The denominator is positive, since every weight is positive.

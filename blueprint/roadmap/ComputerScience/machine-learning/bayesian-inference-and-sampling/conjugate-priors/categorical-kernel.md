# The categorical likelihood

For $n \in \mathbb{N}$, the categorical likelihood is the
kernel from parameters $\theta \in \mathbb{R}^{n+1}$ to labels $\{0, \dots, n\}$ that sends a
probability vector $\theta$ (all $\theta_i \ge 0$ and $\sum_i \theta_i = 1$) to the law of one
label drawn with probability $\theta_i$ for label $i$, and sends every other $\theta$ to the
point mass at label $0$.

Parameters outside the probability vectors form a null set under a Dirichlet prior.

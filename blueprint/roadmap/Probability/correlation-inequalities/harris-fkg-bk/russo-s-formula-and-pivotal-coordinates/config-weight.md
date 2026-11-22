# Bernoulli product weight of a configuration

Let $E$ be a finite set and $p \in \mathbb{R}$. The weight of a configuration $\omega \in \{0,1\}^E$ is the product of its [coordinate weights](edge-weight.md),

$$W_p(\omega) = \prod_{e \in E} w_p(\omega, e) = p^{|\{e : \omega(e) = 1\}|}(1-p)^{|\{e : \omega(e) = 0\}|}.$$

For $p \in [0,1]$ it is the probability of $\omega$ under independent Bernoulli($p$) coordinates.

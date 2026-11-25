# Weight of an anisotropic bond configuration

Let $p_h, p_v \in \mathbb{R}$, $a, b \in \mathbb{N}$, and let $\omega$ be an open/closed configuration of the edges of the box $[0, a] \times [0, b]$ of $\mathbb{Z}^2$. Its weight is

$$w_{p_h, p_v}(\omega) = \prod_{e \text{ horizontal}} \begin{cases} p_h & \omega(e) \text{ open} \\ 1 - p_h & \omega(e) \text{ closed} \end{cases} \;\cdot \prod_{e \text{ vertical}} \begin{cases} p_v & \omega(e) \text{ open} \\ 1 - p_v & \omega(e) \text{ closed,} \end{cases}$$

the product over all edges of the box. For $p_h, p_v \in [0, 1]$ this is the probability of $\omega$ when horizontal edges are open with probability $p_h$, vertical edges with probability $p_v$, all independently; the formula is used for every real $p_h, p_v$.

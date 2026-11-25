# Primal-edge map of two faces lands in a subgraph

For a simple graph $H$ on $\mathbb{Z}^2$ and faces $a, b \in \mathbb{Z}^2$ (labelled by lower left corners), this holds when $S(a, b)$ or $S(b, a)$ is an edge of $H$, where $S$ is the total map

$$S(a, b) = \begin{cases} \{(a_0, m_1), (a_0 + 1, m_1)\} & \text{if } a_0 = b_0, \\ \{(m_0, a_1), (m_0, a_1 + 1)\} & \text{otherwise,} \end{cases} \qquad m_i = \max(a_i, b_i).$$

When $a$ and $b$ are adjacent faces, $S(a, b) = S(b, a)$ is the primal edge separating them; for faces that are not adjacent the two values can differ and need not separate them (for $a = (0, 0)$, $b = (2, 1)$ they are $\{(2, 0), (2, 1)\}$ and $\{(2, 1), (2, 2)\}$).

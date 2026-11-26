# Piecewise radiator solutions are continuous across switches

Let $C, K \in \mathbb{R}$, let $\tau_0 < \tau_1 < \cdots$ be strictly increasing switch times, let $m \in \mathbb{N}$, and let $Q_j$ be the heat input of mode $j$, with radiator rate $r_j(T) = (Q_j - K T^4)/C$, which for $C = 0$ takes the convention $x/0 = 0$. Suppose that for every $j < m$ the temperature $T : \mathbb{R} \to \mathbb{R}$ is continuous on $[\tau_j, \tau_{j+1}]$ and satisfies $T'(t) = r_j(T(t))$ for every $t \in (\tau_j, \tau_{j+1})$. Then $T$ is continuous on $[\tau_0, \tau_m]$.

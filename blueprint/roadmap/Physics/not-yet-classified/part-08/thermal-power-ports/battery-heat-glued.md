# Battery heat in the piecewise radiator equation

Let $C > 0$ and $K \in \mathbb{R}$, let $\tau_0 < \tau_1 < \cdots$ be a strictly increasing sequence of switch times, let $m \in \mathbb{N}$, and for each mode $j$ let $Q^{\mathrm{env}}_j$ be an environmental heat input and $P^c_j, P^d_j$ battery charge and discharge powers. With efficiencies $\eta_c, \eta_d$ the battery heat is $q_j = (1 - \eta_c) P^c_j + (1/\eta_d - 1) P^d_j$, where for $\eta_d = 0$ the convention $1/0 = 0$ applies, and the radiator rate of mode $j$ is

$$r_j(T) = \frac{Q^{\mathrm{env}}_j + q_j - K T^4}{C}.$$

Suppose that for every $j < m$ the temperature $T : \mathbb{R} \to \mathbb{R}$ is continuous on $[\tau_j, \tau_{j+1}]$ and satisfies $T'(t) = r_j(T(t))$ for every $t \in (\tau_j, \tau_{j+1})$. Then $T$ is continuous on $[\tau_0, \tau_m]$, and for every $j < m$ and every $t \in [\tau_j, \tau_{j+1}]$,

$$T(t) - T(\tau_j) = \int_{\tau_j}^{t} r_j(T(s))\,ds.$$

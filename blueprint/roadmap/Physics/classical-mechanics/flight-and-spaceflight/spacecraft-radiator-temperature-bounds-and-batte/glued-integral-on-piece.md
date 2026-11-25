# Integral form of a piecewise radiator solution

Let $C > 0$ and $K_{\mathrm{rad}}$ real. Let $m \in \mathbb{N}$, switch times $\tau : \mathbb{N} \to \mathbb{R}$ strictly increasing, mode heat inputs $Q : \mathbb{N} \to \mathbb{R}$ and $T : \mathbb{R} \to \mathbb{R}$ such that for every $j < m$, $T$ is continuous on $[\tau_j, \tau_{j+1}]$ and $T'(t) = r_j(T(t))$ for every $t \in (\tau_j, \tau_{j+1})$, where $r_j(T) = (Q_j - K_{\mathrm{rad}} T^4)/C$. Then for every $j < m$ and $t \in [\tau_j, \tau_{j+1}]$,

$$T(t) - T(\tau_j) = \int_{\tau_j}^{t} \frac{Q_j - K_{\mathrm{rad}} T(s)^4}{C}\, ds.$$

# Piecewise radiator solution stays in the box across mode switches

Let $C$, $K_{\mathrm{rad}}$, $T_{\min}$, $T_{\max}$ be real. Let $m \in \mathbb{N}$, switch times $\tau : \mathbb{N} \to \mathbb{R}$ strictly increasing, mode heat inputs $Q : \mathbb{N} \to \mathbb{R}$ and $T : \mathbb{R} \to \mathbb{R}$ such that for every $j < m$, $T$ is continuous on $[\tau_j, \tau_{j+1}]$ and $T'(t) = r_j(T(t))$ for every $t \in (\tau_j, \tau_{j+1})$, where $r_j(T) = (Q_j - K_{\mathrm{rad}} T^4)/C$. Assume that for every $j < m$, if $T(\tau_j) \in [T_{\min}, T_{\max}]$ then $T(t) \in [T_{\min}, T_{\max}]$ for every $t \in [\tau_j, \tau_{j+1}]$, and that $T(\tau_0) \in [T_{\min}, T_{\max}]$. Then $T(t) \in [T_{\min}, T_{\max}]$ for every $t \in [\tau_0, \tau_m]$.

Real division by zero is $0$, so at zero heat capacity $C = 0$ every radiator rate is $0$ by convention.

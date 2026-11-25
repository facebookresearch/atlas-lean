# Feasible directions at a design in a stiffness interval

For real $k_{\min}$, $k_{\max}$ and a design $k$, a direction $d \in \mathbb{R}$ is feasible when
some $\varepsilon > 0$ keeps every step in the interval:

$$k + t\, d \in [k_{\min}, k_{\max}] \quad \text{for all } 0 < t \le \varepsilon.$$

The definition puts no condition on the inputs. At a design in the open interval
$(k_{\min}, k_{\max})$ [every direction is feasible](feasible-directions-interior.md); for
$k_{\min} < k_{\max}$ the feasible directions are
[$d \ge 0$ at $k_{\min}$](feasible-directions-left.md) and
[$d \le 0$ at $k_{\max}$](feasible-directions-right.md); and for $k_{\min} = k_{\max} = k$
[only $d = 0$ is feasible](feasible-directions-self.md).
# Clipped radiator solution solves the radiator equation on the box

Let $C$, $K_{\mathrm{rad}}$, $Q$, $T_{\min}$, $T_{\max}$, $s$ be real and $T : \mathbb{R} \to \mathbb{R}$. If $T$ has derivative $r_{\mathrm{clip}}(T(s))$ within $[0, \infty)$ at $s$, where $r_{\mathrm{clip}}(T) = (Q - K_{\mathrm{rad}}\operatorname{clip}(T)^4)/C$ and $\operatorname{clip}(T) = \min(\max(T, T_{\min}), T_{\max})$, and $T(s) \in [T_{\min}, T_{\max}]$, then $T$ has derivative $r(T(s))$ within $[0, \infty)$ at $s$, where $r(T) = \frac{Q - K_{\mathrm{rad}} T^4}{C}$.

Real division by zero is $0$, so at zero heat capacity $C = 0$ every radiator rate is $0$ by convention.

# Lipschitz bound for the clipped radiator rate

Let $C > 0$, $K_{\mathrm{rad}} > 0$, $Q \in \mathbb{R}$ and $0 \le T_{\min} \le T_{\max}$. For all real $a$, $b$,

$$|r_{\mathrm{clip}}(a) - r_{\mathrm{clip}}(b)| \le \frac{K_{\mathrm{rad}} \cdot 4 T_{\max}^3}{C}\, |a - b|,$$

where $r_{\mathrm{clip}}(T) = (Q - K_{\mathrm{rad}}\operatorname{clip}(T)^4)/C$ and $\operatorname{clip}(T) = \min(\max(T, T_{\min}), T_{\max})$.

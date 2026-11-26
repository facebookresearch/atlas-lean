# Clipped radiator temperature rate

For real $C$, $K_{\mathrm{rad}}$, $Q$, $T_{\min}$, $T_{\max}$ and $T$, the clipped radiator rate is the radiator rate $r(T) = \frac{Q - K_{\mathrm{rad}} T^4}{C}$ evaluated at the clipped temperature:

$$r_{\mathrm{clip}}(T) = r(\operatorname{clip}(T)), \qquad \operatorname{clip}(T) = \min(\max(T, T_{\min}), T_{\max}).$$

It is defined for every real $T$ and agrees with $r$ on $[T_{\min}, T_{\max}]$ when $T_{\min} \le T_{\max}$.

Real division by zero is $0$, so at zero heat capacity $C = 0$ every radiator rate is $0$ by convention.

# Zero net energy change over a returning horizon

Let $L > 0$, $C > 0$, $R > 0$ and $V_{\mathrm{in}} \in \mathbb{R}$, let $s, i, v : \mathbb{R} \to \mathbb{R}$ be the switching function, inductor current and capacitor voltage, and let $E(t) = \tfrac12 L\, i(t)^2 + \tfrac12 C\, v(t)^2$ be the stored energy. Let $T \ge 0$, $a = 0$, $b = T$. Let $n \in \mathbb{N}$ and breakpoints $\tau_0 = a$, $\tau_n = b$ with $\tau_k < \tau_{k+1}$ for $k < n$. Assume:

- $i$ and $v$ are continuous on $[a, b]$;
- for each $k < n$ there is $c_k \in \{0, 1\}$ with $s(t) = c_k$ for all $t \in (\tau_k, \tau_{k+1})$;
- for each $k < n$ and $t \in (\tau_k, \tau_{k+1})$, $i$ and $v$ are differentiable at $t$ and $L\, i'(t) = s(t) V_{\mathrm{in}} - v(t)$, $C\, v'(t) = i(t) - v(t)/R$;
- $t \mapsto s(t) V_{\mathrm{in}} i(t) - v(t)^2/R$ is interval integrable on $[a, b]$.

If moreover $i(T) = i(0)$ and $v(T) = v(0)$, then

$$E(T) - E(0) = 0 \qquad\text{and}\qquad \int_0^T \left( s(t)\, V_{\mathrm{in}}\, i(t) - \frac{v(t)^2}{R} \right) dt = 0.$$

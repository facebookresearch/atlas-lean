# Buck converter energy balance between switches

Let $L > 0$, $C > 0$, $R > 0$ and $V_{\mathrm{in}} \in \mathbb{R}$, let $s, i, v : \mathbb{R} \to \mathbb{R}$ be the switching function, inductor current and capacitor voltage, and let $E(t) = \tfrac12 L\, i(t)^2 + \tfrac12 C\, v(t)^2$ be the stored energy. Let $t$ be a time at which $i$ and $v$ are differentiable and the state laws

$$L\, i'(t) = s(t) V_{\mathrm{in}} - v(t), \qquad C\, v'(t) = i(t) - \frac{v(t)}{R}$$

hold. Then $E$ is differentiable at $t$ with

$$E'(t) = s(t)\, V_{\mathrm{in}}\, i(t) - \frac{v(t)^2}{R}.$$

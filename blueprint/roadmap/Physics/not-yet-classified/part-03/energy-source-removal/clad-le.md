# Clad-temperature envelope for a cosine-heated coolant channel

Let $\dot m > 0$, $c_p > 0$, $q_0 \ge 0$, $0 < L \le L_e$, $h > 0$ and $P > 0$. Let $q'(z) = q_0 \cos(\pi z / L_e)$ be the chopped-cosine linear power, and let $T$ be a steady coolant profile on the heated length with inlet temperature $T_{\mathrm{in}}$: $T(-L/2) = T_{\mathrm{in}}$ and, at every $z \in [-L/2, L/2]$, $T$ is differentiable with $\dot m\, c_p\, T'(z) = q'(z)$. Let

$$T_{\mathrm{out}} = T_{\mathrm{in}} + \frac{2 q_0 L_e \sin(\pi L / (2 L_e))}{\pi \dot m c_p}.$$

If the clad temperature $T_{\mathrm{clad}}$ obeys the film law $h P\,(T_{\mathrm{clad}}(z) - T(z)) = q'(z)$ for every $z \in [-L/2, L/2]$, then for every $z \in [-L/2, L/2]$

$$T_{\mathrm{clad}}(z) \le T_{\mathrm{out}} + \frac{q_0}{h P}.$$

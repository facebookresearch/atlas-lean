# Solution of the Michaelis–Menten system on a time window

For real $k_1, k_b, k_2, e_0$ and $t_1$, functions $s, c : \mathbb{R} \to \mathbb{R}$ solve the
Michaelis–Menten system with total enzyme $e_0$ on the window $[0, t_1]$ when, at every
$t \in [0, t_1]$, they have two-sided derivatives with

$$s' = -k_1 (e_0 - c)\, s + k_b c, \qquad c' = k_1 (e_0 - c)\, s - (k_b + k_2)\, c,$$

the free enzyme being $e = e_0 - c$. Outside the window, $s$ and $c$ are constrained only through
their two-sided derivatives at $0$ and $t_1$; for $t_1 < 0$ the window is empty and every pair
$(s, c)$ qualifies.

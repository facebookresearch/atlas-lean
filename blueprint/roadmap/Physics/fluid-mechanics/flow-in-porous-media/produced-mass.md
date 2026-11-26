# Produced mass of a constant pore volume between two pressures

For real $V_p$, $\rho_0$, $c_f$, $p_0$ and $p$, the mass produced on taking a constant pore volume
$V_p$ from pressure $p_0$ to pressure $p$ is the initial minus the current inventory,

$$\Delta M = V_p \bigl(\rho(p_0) - \rho(p)\bigr)$$

for the [exponential density law](density.md) $\rho(p) = \rho_0 e^{c_f (p - p_0)}$. It is defined
for all real inputs, and it is $0$ when $V_p = 0$, $\rho_0 = 0$, $c_f = 0$ or $p = p_0$. For
$V_p, \rho_0, c_f > 0$ it is [positive on depletion](produced-mass-pos.md), $p < p_0$, and
[negative on injection](produced-mass-neg-of-pressure-increase.md), $p > p_0$. In the physical
reading the pore volume $V_p$, the reference density $\rho_0$ and the fluid compressibility $c_f$
are positive.

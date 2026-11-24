# Produced mass of a constant pore volume between two pressures

For real $V_p$, $\rho_0$, $c_f$, $p_0$ and $p$, the mass produced on taking a constant pore volume
$V_p$ from pressure $p_0$ to pressure $p$ is the initial minus the current inventory,

$$\Delta M = V_p \bigl(\rho(p_0) - \rho(p)\bigr)$$

for the [exponential density law](density.md) $\rho(p) = \rho_0 e^{c_f (p - p_0)}$. It is defined
for all real inputs. For $V_p, \rho_0, c_f > 0$ it is positive on depletion ($p < p_0$) and negative
on injection ($p > p_0$). It is $0$ when $V_p = 0$, $\rho_0 = 0$, $c_f = 0$ or $p = p_0$, and
changing the sign of one of $V_p$, $\rho_0$, $c_f$ reverses its sign. In the physical reading the
pore volume $V_p$, the reference density $\rho_0$ and the fluid compressibility $c_f$ are positive.

# Retardation factor of a linearly sorbing solute

For saturated transport with linear sorption, with porosity `phi`, dry bulk density `rho_b` and
distribution coefficient `Kd`, the retardation factor is `R = 1 + rho_b * Kd / phi`. It is defined
for all real `phi`, `rho_b` and `Kd`: with the convention `x / 0 = 0` it is `1` when `phi = 0`. The
intended domain is `phi > 0`, `rho_b ≥ 0` and `Kd ≥ 0`.

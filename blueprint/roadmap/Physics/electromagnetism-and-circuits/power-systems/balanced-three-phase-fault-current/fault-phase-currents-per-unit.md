# For positive bases, the fault phase current formula holds per unit

For complex $E$, $Z_{\mathrm{th}}$ and $Z_f$, real phase voltage and current bases $V_b > 0$ and
$I_b > 0$, and each phase $p = 0, 1, 2$ in the integers modulo 3 (phases $a$, $b$, $c$), the $p$-th
[fault phase current](fault-phase-currents.md) divided by $I_b$ is the $p$-th fault phase current of
the per-unit data $E_{\mathrm{pu}}$, $Z_{\mathrm{th,pu}}$ and $Z_{f,\mathrm{pu}}$, where
$E_{\mathrm{pu}} = E / V_b$ is the per-unit source
[voltage](../per-unit-system-for-three-phase-quantities/voltage-per-unit.md),
$Z_{\mathrm{pu}} = Z / Z_b$ the per-unit
[impedance](../per-unit-system-for-three-phase-quantities/impedance-per-unit.md) of each impedance
$Z$, and $Z_b = V_b / I_b$ the
[impedance base](../per-unit-system-for-three-phase-quantities/impedance-base.md). So the per-unit
phase currents are $(I_{f,\mathrm{pu}}, \alpha^2 I_{f,\mathrm{pu}}, \alpha I_{f,\mathrm{pu}})$,
where $I_{f,\mathrm{pu}} = E_{\mathrm{pu}} / (Z_{\mathrm{th,pu}} + Z_{f,\mathrm{pu}})$ and
$\alpha = e^{2\pi i/3}$ is the
[rotation operator](../symmetrical-components-of-three-phase-systems/alpha.md). When
$Z_{\mathrm{th}} + Z_f = 0$ both sides are $0$ by the convention $x / 0 = 0$.

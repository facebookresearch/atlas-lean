# For positive bases, fault current is current base times per-unit value

For complex $E$, $Z_{\mathrm{th}}$ and $Z_f$ and real phase voltage and current bases $V_b > 0$ and
$I_b > 0$, the [fault current](fault-current.md) is the current base times the fault current formula
applied to the per-unit source voltage and impedances:

$$I_f = I_b\, \frac{E_{\mathrm{pu}}}{Z_{\mathrm{th,pu}} + Z_{f,\mathrm{pu}}},$$

where $E_{\mathrm{pu}} = E / V_b$ is the per-unit source
[voltage](../per-unit-system-for-three-phase-quantities/voltage-per-unit.md),
$Z_{\mathrm{pu}} = Z / Z_b$ the per-unit
[impedance](../per-unit-system-for-three-phase-quantities/impedance-per-unit.md) of each impedance
$Z$, and $Z_b = V_b / I_b$ the
[impedance base](../per-unit-system-for-three-phase-quantities/impedance-base.md). When
$Z_{\mathrm{th}} + Z_f = 0$ both sides are $0$ by the convention $x / 0 = 0$.

# With nonzero total impedance: fault solution, sequences, per-unit form

Let $E$, $Z_{\mathrm{th}}$ and $Z_f$ be complex numbers with $Z_{\mathrm{th}} + Z_f \neq 0$, and let
$V_b > 0$ and $I_b > 0$ be real phase voltage and current bases. Write
$I_f = E / (Z_{\mathrm{th}} + Z_f)$ for the [fault current](fault-current.md). Then:

- for all complex $V$ and $I$, the [Thévenin fault laws](is-thevenin-fault.md)
  $V = E - Z_{\mathrm{th}}\, I$ and $V = Z_f\, I$ hold if and only if $I = I_f$ and $V = Z_f\, I_f$;
- the [fault phase currents](fault-phase-currents.md) $(I_f, \alpha^2 I_f, \alpha I_f)$, where
  $\alpha = e^{2\pi i/3}$ is the
  [rotation operator](../symmetrical-components-of-three-phase-systems/alpha.md), have
  [zero-sequence](../symmetrical-components-of-three-phase-systems/zero-sequence.md) component $0$,
  [positive-sequence](../symmetrical-components-of-three-phase-systems/positive-sequence.md)
  component $I_f$ and
  [negative-sequence](../symmetrical-components-of-three-phase-systems/negative-sequence.md)
  component $0$;
- the per-unit fault current is
  $I_f / I_b = E_{\mathrm{pu}} / (Z_{\mathrm{th,pu}} + Z_{f,\mathrm{pu}})$, where
  $E_{\mathrm{pu}} = E / V_b$ is the per-unit source
  [voltage](../per-unit-system-for-three-phase-quantities/voltage-per-unit.md),
  $Z_{\mathrm{pu}} = Z / Z_b$ the per-unit
  [impedance](../per-unit-system-for-three-phase-quantities/impedance-per-unit.md) of each impedance
  $Z$, and $Z_b = V_b / I_b$ the
  [impedance base](../per-unit-system-for-three-phase-quantities/impedance-base.md).

In a power system the impedances have nonnegative real parts; the statement holds for all complex
values with $Z_{\mathrm{th}} + Z_f \neq 0$.

## Sources

- J. J. Grainger and W. D. Stevenson Jr., *Power System Analysis*, McGraw-Hill (1994).

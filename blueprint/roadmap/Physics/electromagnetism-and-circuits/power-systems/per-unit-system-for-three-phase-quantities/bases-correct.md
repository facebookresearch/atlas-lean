# For positive bases, Ohm's law, power and Z_b are consistent per unit

For real phase bases $V_b > 0$ and $I_b > 0$, three statements hold:

- [Ohm's law](ohm-per-unit-iff.md) is preserved: for all complex $V$, $Z$ and $I$,
  $V = Z I$ if and only if $V_{\mathrm{pu}} = Z_{\mathrm{pu}}\, I_{\mathrm{pu}}$;
- [balanced power](three-phase-power-per-unit.md) is preserved: for all complex $V$ and $I$,
  $3 V \bar I / S_b = V_{\mathrm{pu}}\, \overline{I_{\mathrm{pu}}}$;
- the [impedance base](impedance-base-eq-line-voltage-base-sq-d.md) is
  $Z_b = V_{L,b}^2 / S_b$.

Here $V_{\mathrm{pu}} = V / V_b$, $I_{\mathrm{pu}} = I / I_b$, $Z_{\mathrm{pu}} = Z / Z_b$,
$Z_b = V_b / I_b$, $S_b = 3 V_b I_b$ and $V_{L,b} = \sqrt{3}\, V_b$.

# For nonzero total impedance, fault current and voltage solve the laws

For complex $E$, $Z_{\mathrm{th}}$ and $Z_f$ with $Z_{\mathrm{th}} + Z_f \neq 0$, the
[fault current](fault-current.md) $I_f$ and the [fault voltage](fault-voltage.md) $V_f$ satisfy both
[Thévenin fault laws](is-thevenin-fault.md): $V_f = E - Z_{\mathrm{th}}\, I_f$ and
$V_f = Z_f\, I_f$. The hypothesis is needed when $E \neq 0$: for $Z_{\mathrm{th}} + Z_f = 0$ the
convention $x / 0 = 0$ gives $I_f = V_f = 0$, and the first law fails.

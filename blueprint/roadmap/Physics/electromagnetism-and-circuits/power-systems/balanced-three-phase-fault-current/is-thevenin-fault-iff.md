# With nonzero total impedance, the fault laws have exactly one solution

For complex $E$, $Z_{\mathrm{th}}$, $Z_f$, $V$ and $I$ with $Z_{\mathrm{th}} + Z_f \neq 0$, the
[Thévenin fault laws](is-thevenin-fault.md) $V = E - Z_{\mathrm{th}}\, I$ and $V = Z_f\, I$ hold if
and only if

$$I = I_f = \frac{E}{Z_{\mathrm{th}} + Z_f} \quad \text{and} \quad V = V_f = Z_f\, I_f,$$

the [fault current](fault-current.md) and the [fault voltage](fault-voltage.md). For a zero total
impedance the laws have [no solution](not-is-thevenin-fault-of-total-eq-zero.md) when $E \neq 0$ and
[are solved by every current](is-thevenin-fault-of-total-eq-zero.md) when $E = 0$.

## Sources

- J. J. Grainger and W. D. Stevenson Jr., *Power System Analysis*, McGraw-Hill (1994).

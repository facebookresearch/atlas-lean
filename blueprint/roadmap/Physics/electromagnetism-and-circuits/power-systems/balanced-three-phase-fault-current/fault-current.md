# Fault current: source voltage over total impedance

For complex $E$, $Z_{\mathrm{th}}$ and $Z_f$, the fault current is

$$I_f = \frac{E}{Z_{\mathrm{th}} + Z_f}.$$

With the convention $x / 0 = 0$, $I_f = 0$ when the total impedance $Z_{\mathrm{th}} + Z_f$ is $0$.
For $Z_{\mathrm{th}} + Z_f \neq 0$ it is the only current that satisfies the
[Thévenin fault laws](is-thevenin-fault.md) ([unique solution](is-thevenin-fault-iff.md)). For
$Z_{\mathrm{th}} + Z_f = 0$ the laws have [no solution](not-is-thevenin-fault-of-total-eq-zero.md)
when $E \neq 0$, and [every current solves them](is-thevenin-fault-of-total-eq-zero.md) when
$E = 0$.

## Sources

- J. J. Grainger and W. D. Stevenson Jr., *Power System Analysis*, McGraw-Hill (1994).

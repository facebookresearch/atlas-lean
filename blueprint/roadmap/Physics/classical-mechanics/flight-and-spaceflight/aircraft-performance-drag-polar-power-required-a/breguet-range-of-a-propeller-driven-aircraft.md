# Breguet range of a propeller-driven aircraft

Consider steady level cruise at constant air speed $V > 0$ in which lift equals weight $W(t) > 0$ and thrust equals drag $D$, with constant
lift-to-drag ratio $\Lambda = L/D > 0$ and propeller efficiency $\eta_p \in (0, 1]$, the shaft power $P$ delivering the propulsive power
$\eta_p P = D V$, and fuel burned at the rate $-\,dW/dt = c\,P$ with a constant power-specific fuel consumption $c > 0$ (fuel weight per
unit energy). Then the distance flown while the weight decreases from $W_0$ to $W_1$, $0 < W_1 < W_0$, is

$$R = \frac{\eta_p}{c}\,\frac{L}{D}\,\ln\frac{W_0}{W_1}.$$

**Proof.** Since $D = W/\Lambda$, the power balance gives $-\,dW/dt = c\,D V/\eta_p = c_W\,W/\Lambda$ with $c_W = cV/\eta_p > 0$, the fuel law
of the constant-speed cruise. Its range is $V\,(\Lambda/c_W)\ln(W_0/W_1) = (\eta_p/c)\,\Lambda\,\ln(W_0/W_1)$.

## Proof depends on

- [Range of a cruise at constant air speed](cruise-range-eq.md): the range of the constant-speed cruise under the fuel law $W' = -c_W W/\Lambda$

## Sources

- J. D. Anderson, *Aircraft Performance and Design*, McGraw-Hill, 1999, for the Breguet range equation.

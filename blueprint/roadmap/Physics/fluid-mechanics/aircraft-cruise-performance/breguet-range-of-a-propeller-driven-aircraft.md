# Breguet range of a propeller-driven aircraft

This node covers the Breguet range formula for propeller aircraft. Consider steady level cruise in which lift equals weight $W(t)$ and
thrust equals drag, the lift-to-drag ratio $L/D > 0$ and the propeller efficiency $\eta_p \in (0, 1]$ are constant, and fuel is burned at the
rate $-\,dW/dt = c\,P$, where $P$ is the shaft power and $c > 0$ is a constant power-specific fuel consumption (fuel weight per unit energy).
Then the distance flown while the weight decreases from $W_0$ to $W_1$, $0 < W_1 < W_0$, is

$$R = \frac{\eta_p}{c}\,\frac{L}{D}\,\ln\frac{W_0}{W_1}.$$

## Expansion

A good expansion fixes the units of $c$ and the power balance $\eta_p P = D V$, writes $dR = V\,dt$, and integrates in $W$. The
jet-aircraft version with thrust-specific fuel consumption, and climb, take-off and non-isothermal atmosphere models, are separate nodes.

## Sources

- J. D. Anderson, *Aircraft Performance and Design*, McGraw-Hill, 1999, for the Breguet range equation.

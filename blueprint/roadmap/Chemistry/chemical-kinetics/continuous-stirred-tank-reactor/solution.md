# Concentration in a continuous stirred-tank reactor

For real numbers $V$, $Q$, $k$, $c_{\mathrm{in}}$, $c_0$ and $t$, let

$$c(t) = c_{\mathrm{ss}} + (c_0 - c_{\mathrm{ss}})\, e^{-(Q / V + k) t} ,$$

where $c_{\mathrm{ss}} = Q c_{\mathrm{in}} / (Q + kV)$ is the [steady concentration](steady.md) and a
quotient by zero is read as $0$: $Q / V = 0$ when $V = 0$, and $c_{\mathrm{ss}} = 0$ when $Q + kV = 0$.
For all inputs [it starts at $c_0$](solution-initial.md). When $V > 0$, $Q > 0$ and $k \ge 0$, it is
the concentration at time $t$ in a well-mixed reactor of volume $V$ with volumetric flow $Q$,
first-order rate constant $k$, inlet concentration $c_{\mathrm{in}}$ and initial concentration $c_0$:
it then [solves the reactor equation](solution-has-deriv-at.md)
$V c' = Q (c_{\mathrm{in}} - c) - k V c$.

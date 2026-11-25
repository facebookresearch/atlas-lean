# Solution of the FitzHugh–Nagumo system

For real parameters `a`, `b`, `ε` and `I`, functions `v, w : ℝ → ℝ` solve the FitzHugh–Nagumo system
if at every time `t ≥ 0`

`v'(t) = v(t) - v(t)³/3 - w(t) + I` and `w'(t) = ε (v(t) + a - b w(t))`,

as two-sided derivatives, also at `t = 0`. No initial condition is imposed, and the equations are
required only at times `t ≥ 0`. In the model `b > 0` and `ε > 0`; the definition allows any real
parameters.

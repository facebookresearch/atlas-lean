# Complex velocity of a stream past a cylinder with circulation

For real `a`, `U`, `Γ`, `α` and complex `ζ`, the circle-plane complex velocity is
`w(ζ) = U(e^{−iα} − a² e^{iα}/ζ²) + Γ/(2πi ζ)`. It is meant for `ζ ≠ 0`; with the convention
`x/0 = 0` its value at `ζ = 0` is `U e^{−iα}`.

In the model, `a > 0` is the radius of a cylinder centred at `0`, the flow region is `‖ζ‖ ≥ a`, `U`
is the free-stream speed, `α` the angle of attack to the real axis (free stream `U(cos α, sin α)`)
and `Γ` the circulation about the cylinder (`Γ > 0` counterclockwise); `w` is read as `u − iv`. At
`α = 0` and `ζ ≠ 0` its real and imaginary parts are the cylinder velocity components `u` and `−v`
([cylinder form](circle-velocity-zero-eq-cyl.md)). Under the Joukowski map it is the numerator of
the [physical velocity](physical-velocity.md), and its vanishing at `ζ = a` is the Kutta condition
of the model, which for `a > 0` [forces](kutta-cancellation.md) `Γ = −4πaU sin α`.

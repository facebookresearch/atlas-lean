# Dfe Lyapunov

The **Lyapunov function of the disease-free equilibrium** `(N, 0, 0)`:
`V₀(S, E, I) = g(N, S) + E + ((μ + σ) / σ) I`, `g` the Volterra function. Meaningful for
`S > 0`, `N > 0` and `σ > 0`, which every theorem about it assumes; outside that domain Lean's
`log` and division return junk values.

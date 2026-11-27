# For b, ε > 0, solutions exist for all forward time

Let `b > 0`, `ε > 0`, `a` and `I` real. For every initial state `(v₀, w₀)` there are `v, w : ℝ → ℝ`
forming a [solution](is-solution.md) of the FitzHugh–Nagumo system with `v(0) = v₀` and `w(0) = w₀`.
The maximal solution stays, over every interval `[0, T]`, in the [compact](is-compact-energy-le.md)
ellipse of level `max(E(0), C / κ + 1)` ([forward invariance](energy-le.md)), so it cannot leave
every compact set in finite forward time.

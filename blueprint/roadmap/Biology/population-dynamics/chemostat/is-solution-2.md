# Forward solutions of the single-species chemostat

`(S, x)` solves the chemostat with
input concentration `S⁰`, dilution rate `D`, maximal growth rate `m`, half-saturation constant `a`
and yield `y` at every time `t ≥ 0`: `S'(t) = (S⁰ - S(t)) D - (1/y) m S(t) x(t) / (a + S(t))` and
`x'(t) = x(t) (m S(t) / (a + S(t)) - D)`. The derivatives are two-sided (`HasDerivAt`) at `t = 0`
too, so a trajectory given only on `[0, ∞)` must be extended to negative times with these
derivatives at `0`; one that is only right-differentiable at `0` does not qualify. A solution on
an open interval containing `[0, ∞)` qualifies, and negative times matter only through the
derivatives at `0`. Equivalently, `t ↦ ![x t, S t]` has the derivative given by the chemostat
model's vector field `vectorField (mmRate m a) D S⁰ y` at every `t ≥ 0`
(`isSolution_iff_hasDerivAt_vectorField`).

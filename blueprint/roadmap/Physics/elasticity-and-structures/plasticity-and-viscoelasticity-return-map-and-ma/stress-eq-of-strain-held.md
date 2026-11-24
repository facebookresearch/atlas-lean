# Stress eq of strain held

Held-strain relaxation (the stress relaxation test). If a history obeys the canonical
relation for `t ≥ 0` and the strain is held at its initial value `ε 0` there, then for every
`t ≥ 0` the stress is the existing zero-input exponential decay with removal rate
`E / η = 1 / τ`: `σ t = σ 0 * exp (-(E / η) * t)`, a decay to zero since `0 < E / η`. This is
the `amount_bolus` closed form at removal rate `E / η` (Roylance, Example 2). Here `σ 0` is
the stress at the start of the hold; nothing is claimed for `t < 0`.

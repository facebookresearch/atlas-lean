# Discount Factor

Constant-rate discount factor `(1 + r)⁻ᵗ` for a payment at integer date `t`
(source clause: "discount factor at per-period rate `r`"). The financial factor needs a
rate above `-1`; the definition is total in Mathlib style, and at `r = -1` it takes the
junk value `0` for `t ≥ 1` (`0⁻¹ = 0`). Results that use the factor as a discount assume
`1 + r ≠ 0` or `0 < 1 + r` explicitly.

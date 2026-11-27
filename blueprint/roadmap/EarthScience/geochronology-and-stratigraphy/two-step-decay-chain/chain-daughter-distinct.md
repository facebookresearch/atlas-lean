# Daughter inventory of a decay chain with distinct rates

The daughter inventory in a two-step decay chain whose parent, with initial inventory `P0`,
decays at rate `l1` into a daughter, with initial inventory `D0`, that decays at rate `l2 ≠ l1`:
`D(t) = D0 * exp (-l2 * t) + P0 * l1 / (l2 - l1) * (exp (-l1 * t) - exp (-l2 * t))`. It is
defined for all reals, with the convention `x / 0 = 0`: at `l1 = l2` the feeding term vanishes and
the value is `D0 * exp (-l2 * t)`, which solves the daughter equation `D' = l1 * P - l2 * D` only
when `l1 * P0 = 0`. The intended domain is `l1 ≠ l2`; physically `l1, l2 > 0`, `P0, D0 ≥ 0` and
`t ≥ 0`. The repeated-rate formula `(D0 + P0 * l * t) * exp (-l * t)` covers `l1 = l2 = l`.

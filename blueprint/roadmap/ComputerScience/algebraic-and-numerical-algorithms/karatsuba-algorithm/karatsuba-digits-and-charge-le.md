# Karatsuba digits and charge le

Digit-size bounds alongside the declared-charge bound. In base `B ≥ 2`, for inputs below
`B ^ n` with `n ≥ 1`: both inputs have at most `n` base-`B` digits, and each of the six split
quantities (the high and low halves of both inputs and their distances, which are the operands of
the three recursive calls when `n ≥ 2`) has at most `⌈n/2⌉` digits. The final conjunct is the
charge bound of `karatsuba_time_le_rpow`, which holds for arbitrary operands, so this theorem
proves no digit-operation semantics and no cost bound for actual `Nat` arithmetic, division,
or intermediate operations.

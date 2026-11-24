# Individual contribution to the FGT measure

The individual Foster–Greer–Thorbecke contribution at poverty line `z` and poverty-aversion
parameter `α` is the normalized shortfall `((z - y) / z) ^ α` (real power) if income `y` is below
the line, `y < z`, and `0` otherwise. It is the FGT contribution for `z > 0` and `α ≥ 0`; for other
values the formula is still defined, with the conventions `x / 0 = 0`, `0 ^ 0 = 1`, `0 ^ t = 0` for
`t ≠ 0` and `s ^ t = |s| ^ t * cos (π t)` for `s < 0`: at `z = 0` the contribution is `0 ^ α` if
`y < 0` (`1` for `α = 0`, `0` otherwise) and `0` if `y ≥ 0`, and for `z < 0` and `y < z` the base
`(z - y) / z` is negative. The subgroup decomposition of the FGT measure is an identity of finite
averages and holds for every `z` and `α`, so it carries no domain hypothesis.

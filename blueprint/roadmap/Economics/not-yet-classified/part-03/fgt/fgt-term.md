# Fgt Term

Individual Foster–Greer–Thorbecke contribution at poverty line `z` and poverty-aversion
parameter `α`: the normalized shortfall `((z - y) / z) ^ α` if income `y` is below the line,
and `0` otherwise. It is the FGT contribution for `0 < z` and `0 ≤ α`; outside that domain the
value is Lean's totalized junk (e.g. `z = 0` divides by zero). The decomposition theorem below
is an identity of finite averages and holds for every `z` and `α`, so it carries no domain
hypothesis.

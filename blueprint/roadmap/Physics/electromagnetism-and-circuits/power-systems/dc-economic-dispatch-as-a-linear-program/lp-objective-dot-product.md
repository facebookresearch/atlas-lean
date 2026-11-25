# The LP objective is minus the cost of the decoded generation

For cost coefficients `c` and every LP point `x` (nonnegative or not), the value of the
[LP objective](lp-objective.md) at `x` is `-c · p`, where `p` is the
[decoded generation](decode-generation.md) of `x`.

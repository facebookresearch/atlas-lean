# Equal means: a prior/cost-only decision

With `s1 = s0`, positive priors and costs with
`C00 < C10`, `C11 < C01`, the rule ignores the observation: it decides `true` iff
`pi0 (C10 - C00) < pi1 (C01 - C11)`, `tie` on equality, `false` otherwise.

# Payoff of a behavior strategy in a role game

For finite sets `ι` and `κ` of role-I and role-II strategies, a real `ρ`, payoff matrices
`A : ι × κ → ℝ` (role I against role II) and `B : κ × ι → ℝ` (role II against role I), and pairs
`s = (p, q)` and `t = (p', q')` of vectors on `ι` and `κ`, the payoff of `s` against `t` is
`ρ (p · A q') + (1 - ρ) (q · B p')`. When `0 ≤ ρ ≤ 1` and the vectors are
[mixed strategies](../../../Probability/not-yet-classified/is-dist.md), it is the expected payoff of a contestant using `p` in role I and
`q` in role II, placed in role I with probability `ρ` and in role II with probability `1 - ρ`,
against an opponent using `t` in the other role.

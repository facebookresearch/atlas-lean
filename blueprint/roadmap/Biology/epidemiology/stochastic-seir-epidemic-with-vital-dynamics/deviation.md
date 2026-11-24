# Deviation of the scaled chain from a deterministic path

For `N ∈ ℕ`, count paths `S, E, I, R : ℝ → ℕ`, real functions `s`, `e`, `i`, `r` and a time `t`, the
`ℓ¹` distance between the scaled chain `(S, E, I, R) / N` and the deterministic path `(s, e, i, r)`:

`D(t) = |S(t) / N - s(t)| + |E(t) / N - e(t)| + |I(t) / N - i(t)| + |R(t) / N - r(t)|`.

At `N = 0` division by zero gives `0`, so `D(t) = |s(t)| + |e(t)| + |i(t)| + |r(t)|`; the intended
domain is `N ≥ 1`.

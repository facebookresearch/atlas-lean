# The tilted ladder-height law is defective

Let `q` be nonnegative weights and `f` real scores on a finite alphabet, and let `θ` be a real
number with `∑_b q_b e^{θ f(b)} = 1`. Then for every horizon `n`,
`∑_{k ≤ n} E[e^{θ H}; τ₊ = k] ≤ 1`, where `E[e^{θ H}; τ₊ = k]` is the
[weighted average](score-expect.md) over score lists of length `k` of the indicator that the list
[ends at the first strict ascending ladder epoch](is-first-ladder.md) times `e^{θ H}`, with `H` the
ladder height. It comes from optional stopping of `e^{θ S}` at the first ladder epoch; letting
`n → ∞` gives `E[e^{θ H}; τ₊ < ∞] ≤ 1`.

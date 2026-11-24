# Fire

One firing event of the population with phases `φ`: all phases advance by `1 - max φ`, the
`k` oscillators that reach phase `1` fire with strength `s k` and reset to `0`, and every other
oscillator `j` moves to phase `g(f(ψ_j) + s k)` if `f(ψ_j) + s k < 1`, and is absorbed (reset to
`0`) otherwise, where `ψ` are the advanced phases.

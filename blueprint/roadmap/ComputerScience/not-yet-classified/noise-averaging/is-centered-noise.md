# Noise contract

Conditions (a) and (b) of Tsitsiklis (1994), Lemma 1, for one step,
stated with the conditional Lebesgue expectation `μ⁻[· | m]`, so no integrability of `w` is
assumed: the conditional second moment of `w` given `m` is at most `max B 0`, and the
conditional expectations of the positive part `ofReal w` and the negative part `ofReal (-w)`
agree. The bound is `μ⁻[ofReal (w ^ 2) | m] ≤ ofReal B`, and `ENNReal.ofReal` sends a negative
`B` to `0`: for a nonnegative envelope `B` it is the bound by `B` itself, while where `B < 0` it
asks the conditional second moment to vanish, not to be at most `B`. The contract is meant for a
sub-σ-algebra `m ≤ m0` such that `μ.trim` is σ-finite, which holds for every σ-algebra of a
filtration under a finite measure. Square-integrable noise with the usual conditions
`μ[w | m] = 0` and `μ[w ^ 2 | m] ≤ B` satisfies it (`IsCenteredNoise.of_memLp`).

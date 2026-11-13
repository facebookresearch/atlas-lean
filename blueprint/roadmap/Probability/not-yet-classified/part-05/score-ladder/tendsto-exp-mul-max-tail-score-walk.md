# Ladder-height limit for an i.i.d. integer score walk

**Ladder-height limit for an i.i.d. integer score walk** (Cramér–Lundberg /
Karlin–Dembo). Let `X` be i.i.d. integer scores with walk `S`, maximum `M = sup_n S n`, and
ladder-height law `g j = P(τ₊ < ∞, S_{τ₊} = j)`. If `θ > 0` satisfies the ladder Cramér
identity `∑ g j e^{θ j} = 1` (for a negative-drift walk this holds at the root of
`𝔼 e^{θ X} = 1`; here it is a hypothesis, and it forces `P(τ₊ < ∞) < 1`, see
`tsum_lt_one_of_hasSum_exp_mul`), the ladder support is aperiodic and the tilted ladder mean
`μ = ∑ j g j e^{θ j}` is finite, then
`e^{θ k} P(M > k) → (1 - P(τ₊ < ∞)) / ((e^θ - 1) μ)`. The ladder decomposition is proved
(`isRenewalSolution_maxTail`), not assumed.

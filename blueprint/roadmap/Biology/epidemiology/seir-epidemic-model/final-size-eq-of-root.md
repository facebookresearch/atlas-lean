# With E(0) + I(0) > 0, every final-size root x ≤ S(0) equals S∞

Let `(S, E, I, R)` be a [solution of the SEIR system](is-solution.md) with `β ≥ 0`, `σ > 0`,
`γ > 0`, `N > 0`, `S(0), E(0), I(0), R(0) ≥ 0` and a nonzero infected seed `E(0) + I(0) > 0`, write
`R₀ = β / γ`, and suppose `S(t) → S∞` as `t → ∞`. If a real `x ≤ S(0)` solves the final-size
equation

`x = S(0) e^{-R₀ (S(0) + E(0) + I(0) - x) / N}`,

then `x = S∞`. Since `S∞` is itself such a root ([limits and final size](tendsto-final-size.md)), it
is the only root `x ≤ S(0)`: the final size is determined by the initial data. The proof applies the
[uniqueness of the SIR final size](../global-behaviour-of-the-sir-model/final-size-root-unique.md)
with initial infected mass `E(0) + I(0)`.

# Regeneration of a process at a state

Let `P` be a measure on `Ω`, `X : ℝ × Ω → σ` a process with values in a measurable space `σ`,
`R_0, R_1, … : Ω → ℝ` random times and `x₀ ∈ σ`. `X` regenerates at `x₀` at the times `R_k` when:

- at every sample point `ω`, `0 ≤ R_0(ω) < R_1(ω) < R_2(ω) < ⋯` and `X_{R_k(ω)}(ω) = x₀` for
  every `k`;
- the [cycle lengths](cycle-length.md) `L_k = R_{k+1} - R_k` are pairwise independent under `P`,
  and each has the law of `L_0`;
- for every measurable `f : σ → ℝ` with `|f| ≤ B` for some real `B`, the
  [cycle rewards](cycle-reward.md) `W_k(f) = ∫_{R_k}^{R_{k+1}} f(X_s) ds` are pairwise independent
  under `P`, and each has the law of `W_0(f)`;
- the time `∫_{R_0}^{R_1} 1{X_s = x₀} ds` spent in `x₀` during the first cycle is `P`-integrable.

Having the law of `L_0` or of `W_0(f)` includes measurability up to `P`-null sets. Only pairwise
independence is required; nothing relates the lengths to the rewards, and the `R_k` need not be
stopping times or the entrance times into `x₀`. Total mass one is not required of `P` here; the
results that use this definition assume that `P` is a probability measure.

For a continuous-time Markov chain on a countable state space that reaches `x₀` almost surely,
with `x₀` recurrent and not absorbing, the successive entrance times into `x₀` have these
properties once a null set of paths is discarded: by the strong Markov property at the times
`R_k`, the path segments between them are independent and identically distributed (Norris 1997,
§3.4 and Theorem 1.10.1, proof of Theorem 3.8.1). The time spent in `x₀` during a cycle is then
one holding time there, exponential with rate `q(x₀) > 0`, so it has finite mean.

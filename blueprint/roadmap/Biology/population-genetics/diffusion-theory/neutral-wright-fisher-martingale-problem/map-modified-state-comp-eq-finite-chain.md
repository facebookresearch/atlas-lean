# Finite-dimensional laws of the realization

For every `x ∈ [0, 1]`, every `m ∈ ℕ` and all times `τ_0 < τ_1 < ⋯ < τ_{m-1}` in `[0, ∞)`, the law
of `(X_{τ_0}, …, X_{τ_{m-1}})` under the
[canonical path measure](../construction-of-the-neutral-wright-fisher-diffus/raw-measure.md) `P_x`,
where `X` is the
[continuous realization](../construction-of-the-neutral-wright-fisher-diffus/modified-process.md)
started at `x`, is the
[finite-dimensional law](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/finite-chain-law.md)
of the
[neutral Wright–Fisher kernels](../construction-of-the-neutral-wright-fisher-diffus/neutral-kernel.md)
`K` started at `x` at time `0`: for `m > 0`, the law of the Markov chain started at `x` with
transitions `K_{τ_0}`, `K_{τ_1 - τ_0}`, …, `K_{τ_{m-1} - τ_{m-2}}`; for `m = 0` it is the point mass
on the empty tuple.

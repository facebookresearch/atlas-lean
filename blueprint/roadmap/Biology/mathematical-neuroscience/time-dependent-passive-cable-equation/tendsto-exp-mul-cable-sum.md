# For τ > 0 and ℓ, L ≠ 0, e^(t/τ) times the expansion tends to a₀

Let `τ > 0`, `ℓ ≠ 0` and `L ≠ 0` be real numbers, `s` a finite set of natural numbers not
containing `0`, `a_n` real coefficients and `x` a real number. Then the
[finite expansion](cable-sum.md) over `s ∪ {0}`, rescaled by the membrane decay, tends to the
uniform-mode coefficient:

`e^(t/τ) V_{s ∪ {0}}(t, x) → a_0` as `t → ∞`.

This is Rall's equalization: every nonuniform mode decays strictly faster than `1 / τ`
([strict monotonicity](decay-rate-strict-mono.md)). Without `ℓ ≠ 0` and `L ≠ 0` the conclusion
fails in general: if `ℓ = 0` or `L = 0`, every rate equals `1 / τ`, and the rescaled expansion is
the constant `∑_{n ∈ s ∪ {0}} a_n cos (n π x / L)`.

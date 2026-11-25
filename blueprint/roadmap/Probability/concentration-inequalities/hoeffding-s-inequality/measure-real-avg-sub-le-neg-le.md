# Lower-tail Hoeffding inequality for averages

If `Z₁, …, Zₙ` are independent real
random variables with `Zᵢ ∈ [a, b]` almost surely, then for every `t ≥ 0`,
`P((1/n) ∑ Zᵢ - (1/n) ∑ E[Zᵢ] ≤ -t) ≤ exp (-2 n t² / (b - a)²)`. When `a = b` the right-hand side
is `exp 0 = 1` by Lean's convention `x / 0 = 0`. When `n = 0` both sums are empty, so the average
is `0`, and the right-hand side is `exp 0 = 1`: the bound holds trivially.

## Sources

- W. Hoeffding, J. Amer. Statist. Assoc. 58 (1963), Theorem 2, applied to `-Zᵢ`; F. Bach, *Learning Theory from First Principles*, MIT Press (2024), Section 1.2.1, proof of Corollary 1.1.

# Invariance of `|Δ(τ)| (Im τ)⁶` under the modular group

For `τ` in the upper half-plane
let `Δ(τ) = g₂(τ)³ - 27 g₃(τ)²` be the discriminant of the lattice `ℤ τ + ℤ`, where `g₂(τ)` is
sixty times the sum of the inverse fourth powers of the nonzero periods `m τ + n` and `g₃(τ)` is
one hundred forty times the sum of their inverse sixth powers (as in
`MetaMathlibExt.lattice_discriminant_eq_eta_product`, where the sums run over all integer
pairs and the summand of the zero pair is zero).
Then for all integers `a, b, c, d` with `a d - b c = 1`,
`Δ((a τ + b) / (c τ + d)) = (c τ + d)¹² Δ(τ)` and
`Im((a τ + b) / (c τ + d)) = Im τ / |c τ + d|²`, and hence
`|Δ((a τ + b) / (c τ + d))| Im((a τ + b) / (c τ + d))⁶ = |Δ(τ)| (Im τ)⁶`. The same holds with
`η²⁴` in place of `Δ`, for the Dedekind eta function `η`.

## Sources

- J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version <https://jmilne.org/math/Books/EC2.pdf>, Chapter V, §3, Proposition 3.5, p. 191: `Δ = g₄³ - 27 g₆²` is a cusp form of weight 12 for `Γ₀(1)`, with the transformation law (3.1b), p. 191; P. Deligne, Séminaire Bourbaki, exposé 616, Astérisque 121–122 (1985), <http://www.numdam.org/item/SB_1983-1984__26__25_0/>, Remarque 1.5, p. 28: the function `4π y |q^{1/12} ∏ (1 - qⁿ)²|²`, `y = Im(τ)`, is invariant under `SL(2, ℤ)`.

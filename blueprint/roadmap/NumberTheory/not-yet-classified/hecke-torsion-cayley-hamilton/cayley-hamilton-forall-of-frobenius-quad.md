# Cayley–Hamilton on Hecke torsion

Let `J` be a `HeckeAlg`-module with a commuting
action of `AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ`, and let `ρ` be a homomorphism from
that group to the `2 × 2` matrices over `HeckeAlg ⧸ 𝔪`. Assume:

* `p ∈ 𝔪`;
* `FrobeniusQuadratic N p J`, over `ℚ` and in `AlgebraicClosure ℚ`;
* no prime `ℓ ∉ S` divides `N * p`;
* for every prime `ℓ ∉ S`, every valuation subring `A` of `AlgebraicClosure ℚ` lying over
  `ℓ`, and every `σ` that is Frobenius at `ℓ` for `A`, the trace and determinant of `ρ σ`
  are the images of `heckeGen ℓ` and `ℓ` in `HeckeAlg ⧸ 𝔪`;
* `FrobeniusPowerDense S` modulo the intersection of the kernel of `ρ` with the subgroup
  fixing the `𝔪`-torsion of `J`.

Then for every `σ`, every `x` in the `𝔪`-torsion of `J`, and all `t d : HeckeAlg` whose
images in `HeckeAlg ⧸ 𝔪` are the trace and determinant of `ρ σ`, we have
`σ • σ • x - t • (σ • x) + d • x = 0`.

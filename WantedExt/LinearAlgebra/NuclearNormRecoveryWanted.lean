/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.LinearAlgebra.Matrix.LowRankRecovery

/-!
# Exact recovery of low-rank matrices by nuclear norm minimization

If a linear map `𝒜` on `m × n` matrices has restricted isometry constant `δ_{5r}(𝒜) < 1/10`, then
for every matrix `X₀` of rank at most `r`, the minimizer of the nuclear norm over the affine space
`{X : 𝒜(X) = 𝒜(X₀)}` is `X₀` itself (B. Recht, M. Fazel and P. A. Parrilo, *Guaranteed
minimum-rank solutions of linear matrix equations via nuclear norm minimization*, SIAM Review 52
(2010), arXiv:0706.4138, Theorem 3.3). The proof, built on the decomposition of Lemma 3.4 and
modelled on the sparse-vector argument of compressed sensing, is deferred.
-/

@[expose] public section

open Matrix MathlibExt.LinearAlgebra.Matrix.LowRankRecovery

namespace MathlibExt.LinearAlgebra.NuclearNormRecoveryWanted

/-- **Exact recovery by nuclear norm minimization under restricted isometry.** Let `r ≥ 1` and let
`𝒜` be a linear map from real `m × n` matrices to `ℝ^p` that is a restricted isometry of order
`5 r` with a constant `δ < 1/10` (that is, `δ_{5r}(𝒜) < 1/10`). Let `X₀` have rank at most `r`.
Then `X₀` is the unique minimizer of the nuclear norm over `{X : 𝒜(X) = 𝒜(X₀)}`: every other
matrix `X` with `𝒜(X) = 𝒜(X₀)` has `‖X₀‖_* < ‖X‖_*`.

Source: B. Recht, M. Fazel and P. A. Parrilo, *Guaranteed minimum-rank solutions of linear
matrix equations via nuclear norm minimization*, SIAM Review 52 (2010), arXiv:0706.4138,
Theorem 3.3 ("`X_* = X₀`", with `X_*` the nuclear-norm minimizer (3.1) and `X₀` of rank `r`;
rank at most `r` follows, since `δ_{5r'} ≤ δ_{5r}` for `r' ≤ r` and the case `X₀ = 0` is
immediate). -/
theorem_wanted nuclearNorm_lt_of_isRestrictedIsometry_five_mul {m n p : ℕ}
    {𝒜 : Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin p)} {r : ℕ} (hr : 1 ≤ r)
    {δ : ℝ} (hRIP : IsRestrictedIsometry 𝒜 (5 * r) δ) (hδ : δ < 1 / 10)
    {X₀ : Matrix (Fin m) (Fin n) ℝ} (hX₀ : X₀.rank ≤ r) (X : Matrix (Fin m) (Fin n) ℝ)
    (hX : 𝒜 X = 𝒜 X₀) (hne : X ≠ X₀) :
    nuclearNorm X₀ < nuclearNorm X

end MathlibExt.LinearAlgebra.NuclearNormRecoveryWanted

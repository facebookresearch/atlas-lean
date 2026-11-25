/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.Approximation.SparseRecoveryRIP

/-!
# Stable sparse recovery by `ℓ₁` minimization under the restricted isometry property

If the isometry constant of `Φ` satisfies `δ_{2s} < √2 - 1`, then `ℓ₁` minimization recovers every
vector `x` up to an error controlled by its best `s`-term approximation error
`‖x - x_s‖₁`, and, with noisy measurements `y = Φ x + z`, `‖z‖₂ ≤ ε`, up to an additional error
`C₁ ε` (E. J. Candès, *The restricted isometry property and its implications for compressed
sensing*, C. R. Acad. Sci. Paris, Ser. I 346 (2008) 589–592, doi:10.1016/j.crma.2008.03.014,
Theorems 1.2 and 1.3). The noiseless ℓ₁ bound is proved in
`MathlibExt.Analysis.Approximation.SparseRecoveryRIP`. Lemmas 2.1 and 2.2 of that Note, the
uniqueness of sparse solutions and exact recovery of sparse vectors are proved in
`MathlibExt.Analysis.Approximation.SparseRestrictedIsometry`.

Conventions, all as in Candès (2008):

* `δ_{2s} < √2 - 1` is written `HasRIP Φ (2 * s) δ` with `δ < √2 - 1`; the constants below are
  increasing in `δ` on `[0, √2 - 1)`, so the statements for every such `δ` are equivalent to the
  statements at `δ = δ_{2s}`.
* `ρ = √2 δ / (1 - δ)`, `α = 2 √(1 + δ) / (1 - δ)`, `C₀ = 2 (1 + ρ) / (1 - ρ)` and
  `C₁ = 2 α / (1 - ρ)`; these are written out in the statements. Candès (2008) derives
  `‖h‖₂ ≤ 2 (1 - ρ)⁻¹ (α ε + (1 + ρ) e₀)` with `e₀ = s^{-1/2} ‖x - x_s‖₁` and
  `‖h‖₁ ≤ 2 (1 + ρ) (1 - ρ)⁻¹ ‖x - x_s‖₁`, which give these constants. For `δ = 0.2` they are
  `C₀ ≈ 4.19` and `C₁ ≈ 8.47`, matching the values `4.2` and `8.5` quoted after Theorem 1.3.
* `x_s` is `x` with all but its `s` largest entries (in absolute value) set to zero, so
  `‖x - x_s‖₁ = min {∑_{j ∉ S} |x j| | #S ≤ s}`. A bound by `C ‖x - x_s‖₁` is therefore
  equivalent to the bound by `C ∑_{j ∉ S} |x j|` for every `S` with `#S ≤ s`, which is how it is
  stated here.
* "The solution `x̂` of `min ‖x̃‖₁` subject to a constraint" is any feasible `xhat` whose `ℓ₁` norm
  is at most that of every feasible vector.
-/

@[expose] public section

open Finset Matrix MathlibExt.Analysis.Approximation.SparseRestrictedIsometry

namespace MathlibExt.Analysis.Approximation.SparseRecoveryRIPWanted

/-- **Noiseless recovery, `ℓ₂` error** (E. J. Candès, *The restricted isometry property and its
implications for compressed sensing*, C. R. Acad. Sci. Paris, Ser. I 346 (2008) 589–592,
Theorem 1.2, eq. (5)): let `s ≥ 1` and let `Φ` have the restricted isometry property of order
`2 s` with a constant `δ < √2 - 1`. Let `xhat` be a solution of `min ‖x̃‖₁` subject to
`Φ x̃ = Φ x`. Then `‖xhat - x‖₂ ≤ C₀ s^{-1/2} ‖x - x_s‖₁` with `C₀ = 2 (1 + ρ) / (1 - ρ)` and
`ρ = √2 δ / (1 - δ)`; here `‖x - x_s‖₁` is replaced by `∑_{j ∉ S} |x j|` for an arbitrary set
`S` of at most `s` indices, an equivalent formulation since `x_s` is the best `s`-term
approximation of `x`. -/
theorem_wanted sqrt_sum_sq_sub_le_of_hasRIP {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    {Φ : Matrix (Fin m) ι ℝ} {s : ℕ} (hs : 1 ≤ s) {δ : ℝ} (hΦ : HasRIP Φ (2 * s) δ)
    (hδ : δ < √2 - 1) {x xhat : ι → ℝ} (hfeas : Φ *ᵥ xhat = Φ *ᵥ x)
    (hmin : ∀ w : ι → ℝ, Φ *ᵥ w = Φ *ᵥ x → ∑ j, |xhat j| ≤ ∑ j, |w j|)
    {S : Finset ι} (hS : #S ≤ s) :
    √(∑ j, (xhat j - x j) ^ 2) ≤
      2 * (1 + √2 * δ / (1 - δ)) / (1 - √2 * δ / (1 - δ)) / √s * ∑ j ∈ Sᶜ, |x j|

end MathlibExt.Analysis.Approximation.SparseRecoveryRIPWanted

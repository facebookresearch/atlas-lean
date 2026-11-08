/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.SelbergSpectralGap

/-!
# Selberg spectral-gap public-API and boundary checks

Exact-statement exercises for congruence subgroups, the hyperbolic
Laplacian on constants, gap parameters, the proved elementary bounds
`0 ≤ C₆₁ ≤ 1/2`, and the equivalence of `C₆₁ = 0` with the absence of
exceptional eigenvalues.
-/

@[expose] public section

open scoped MatrixGroups

namespace SelbergSpectralGapTest

open MathlibExt.NumberTheory.SelbergSpectralGap

/-- The full modular group is a congruence subgroup. -/
example : IsCongruenceSubgroup (⊤ : Subgroup SL(2, ℤ)) :=
  isCongruenceSubgroup_top

/-- The hyperbolic Laplacian of `(im z)^2` is `-2 (im z)^2`, a
non-holomorphic sanity check that the operator uses real derivatives. -/
example (z : UpperHalfPlane) :
    hyperbolicLaplacian (fun u : UpperHalfPlane => (((u : ℂ).im) ^ 2 : ℝ)) z =
      -2 * (((z : ℂ).im ^ 2 : ℝ) : ℂ) :=
  hyperbolicLaplacian_im_sq z

/-- The hyperbolic Laplacian kills constants. -/
example (c : ℂ) (z : UpperHalfPlane) :
    hyperbolicLaplacian (fun _ => c) z = 0 :=
  hyperbolicLaplacian_const c z

/-- Every gap parameter lies in `[0, 1/2]`. -/
example (Γ : Subgroup SL(2, ℤ)) :
    0 ≤ exceptionalGap Γ ∧ exceptionalGap Γ ≤ 1 / 2 :=
  ⟨zero_le_exceptionalGap Γ, exceptionalGap_le_half Γ⟩

/-- Proved elementary bounds `0 ≤ C₆₁ ≤ 1/2`. -/
example : 0 ≤ selbergConstant ∧ selbergConstant ≤ 1 / 2 :=
  ⟨zero_le_selbergConstant, selbergConstant_le_half⟩

/-- An exceptional eigenvalue `3/16` for a congruence subgroup would
force `1/4 ≤ C₆₁` through its gap contribution `√(1/4 - 3/16) = 1/4`. -/
example {Γ : Subgroup SL(2, ℤ)} (hΓ : IsCongruenceSubgroup Γ)
    (hlam : IsEigenvalue Γ (3 / 16)) : Real.sqrt (1 / 4 - 3 / 16) ≤ selbergConstant :=
  sqrt_le_selbergConstant hΓ hlam (by norm_num) (by norm_num)

/-- Selberg's constant vanishes iff there are no exceptional
eigenvalues. -/
example : selbergConstant = 0 ↔ SelbergEigenvalueConjecture :=
  selbergConstant_eq_zero_iff

end SelbergSpectralGapTest

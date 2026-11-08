/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.ModularForms.SelbergSpectralGap

@[expose] public section

open scoped MatrixGroups

namespace MathlibExt.NumberTheory.SelbergSpectralGap

/-!
# Catalogue bounds for the Selberg congruence spectral-gap constant

The frozen catalogue bounds for constant C61a as proof requests against
`selbergConstant`, the supremum over congruence subgroups of the
exceptional-eigenvalue gap `√(max (0, 1/4 - λ₁(Γ)))` in the smooth
`L²` eigenfunction model of the provider.

The provider proves the elementary bounds `0 ≤ C₆₁ ≤ 1/2` (the
catalogue's trivial lower row `0`) and the equivalence of `C₆₁ = 0` with
the absence of exceptional eigenvalues. The requests below are the
catalogue's two upper rows, in eigenvalue form and in the derived gap
form: Selberg's theorem `λ₁(Γ) ≥ 3/16` (so `C₆₁ ≤ 1/4`) and the
Kim--Sarnak bound `λ₁(Γ) ≥ 975/4096 = 1/4 - (7/64)^2` (so
`C₆₁ ≤ 7/64`). The model-scope gaps recorded in the provider apply:
no self-adjoint spectral theory, discreteness below `1/4`, or
covering-independence of the `L²` condition is formalized.
-/

/-- Source: Selberg, as recorded in Luo--Rudnick--Sarnak (1995): every
eigenvalue of a congruence subgroup in the model is either `0`-side
excluded or at least `3/16`; stated here as the absence of eigenvalues in
`(0, 3/16)`. -/
theorem_wanted selberg_threeSixteenths_wanted
    (Γ : Subgroup SL(2, ℤ)) (hΓ : IsCongruenceSubgroup Γ) (lam : ℝ)
    (hlam : IsEigenvalue Γ lam) :
    ¬ (0 < lam ∧ lam < 3 / 16)

/-- Source: Selberg's theorem `λ₁(Γ) ≥ 3/16`, catalogue upper row
`C₆₁ ≤ 1/4`. -/
theorem_wanted selbergUpperBound_wanted :
    selbergConstant ≤ 1 / 4

/-- Source: Kim--Sarnak (2003), as recorded in
Kim--Ramakrishnan (2003): no eigenvalue of a congruence subgroup lies in
`(0, 975/4096)`. -/
theorem_wanted kimSarnak975_wanted
    (Γ : Subgroup SL(2, ℤ)) (hΓ : IsCongruenceSubgroup Γ) (lam : ℝ)
    (hlam : IsEigenvalue Γ lam) :
    ¬ (0 < lam ∧ lam < 975 / 4096)

/-- Source: Kim--Sarnak bound `λ₁(Γ) ≥ 975/4096 = 1/4 - (7/64)^2`,
catalogue best upper row `C₆₁ ≤ 7/64`. -/
theorem_wanted kimSarnakUpperBound_wanted :
    selbergConstant ≤ 7 / 64

end MathlibExt.NumberTheory.SelbergSpectralGap

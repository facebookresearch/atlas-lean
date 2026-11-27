/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Elliptic.HomothetyClasses

open scoped Pointwise UpperHalfPlane MatrixGroups

namespace PeriodPair

-- Scaling of the invariants, for arbitrary homothetic period pairs.
example {L L' : PeriodPair} {c : ℂ} (hc : c ≠ 0)
    (h : (L'.lattice : Set ℂ) = c • (L.lattice : Set ℂ)) :
    L'.g₂ = c⁻¹ ^ 4 * L.g₂ ∧ L'.g₃ = c⁻¹ ^ 6 * L.g₃ :=
  ⟨g₂_eq_of_lattice_eq_smul hc h, g₃_eq_of_lattice_eq_smul hc h⟩

-- The lattice of `L.scale α` is `α` times that of `L`, so `g₂` scales by `α⁻⁴`.
example (L : PeriodPair) (α : ℂˣ) :
    (L.scale α).g₂ = (α : ℂ)⁻¹ ^ 4 * L.g₂ :=
  g₂_eq_of_lattice_eq_smul α.ne_zero (lattice_scale L α)

example (L : PeriodPair) (α : ℂˣ) :
    1728 * (L.scale α).g₂ ^ 3 / ((L.scale α).g₂ ^ 3 - 27 * (L.scale α).g₃ ^ 2) =
      1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) :=
  jInvariant_eq_of_lattice_eq_smul α.ne_zero (lattice_scale L α)

-- Every period pair is homothetic to some `(1, τ)` with `τ` in the upper half-plane (clause 2).
example (L : PeriodPair) : ∃ τ : ℍ, L.IsHomothetic (ofTau τ τ.im_pos.ne') :=
  homothety_classes.2.1 L

-- The three statements together, with the third from `isHomothetic_ofTau_iff`.
example (τ τ' : ℍ) :
    (ofTau τ τ.im_pos.ne').IsHomothetic (ofTau τ' τ'.im_pos.ne') ↔ ∃ γ : SL(2, ℤ), τ' = γ • τ :=
  homothety_classes.2.2 τ τ'

end PeriodPair

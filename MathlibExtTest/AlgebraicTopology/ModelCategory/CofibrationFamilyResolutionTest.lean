/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrationFamilyResolution
public import Mathlib.AlgebraicTopology.ModelCategory.Instances

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe w u v s

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Cardinal

namespace CofibrationFamilyResolutionTest

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [IsLocallyPresentable.{w} C] {I : Type s} [Small.{w} I]

/-- The two actual weak comparison legs preserve the original arrow's weakness,
even when the original arrow is not a cofibration. -/
theorem original_weak_class_retained (S : I → Arrow C) (fixed : Type w) :
    ∃ (T : I → Arrow C) (r : ∀ i, T i ⟶ S i),
      (∀ i, IsCofibrant (T i).left ∧ Cofibration (T i).hom ∧
        trivialFibrations C (r i).left ∧ trivialFibrations C (r i).right) ∧
        ∀ i, WeakEquivalence (T i).hom ↔ WeakEquivalence (S i).hom := by
  obtain ⟨T, r, κ, hκ, hbot, _, _, _, hResolution, _⟩ :=
    exists_small_cofibration_family_resolution S fixed
  refine ⟨T, r, fun i => ⟨(hResolution i).1,
    (cofibration_iff _).2 (hResolution i).2.1,
    (hResolution i).2.2.1, (hResolution i).2.2.2⟩, ?_⟩
  intro i
  let _ : WeakEquivalence (r i).left :=
    (weakEquivalence_iff _).2 (hResolution i).2.2.1.2
  let _ : WeakEquivalence (r i).right :=
    (weakEquivalence_iff _).2 (hResolution i).2.2.2.2
  rw [← weakEquivalence_postcomp_iff _ (r i).right,
    ← (r i).w, weakEquivalence_precomp_iff]

/-- An empty original indexing type still yields a regular profile bound;
no nonempty-family assumption is used by the constructor. -/
theorem empty_family_profile (fixed : Type w) :
    ∃ (T : PEmpty.{s + 1} → Arrow C) (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      (ℵ₀ : Cardinal.{w}) < κ ∧ HasCardinalLT fixed κ ∧
        ∀ i, IsCofibrant (T i).left := by
  let S : PEmpty.{s + 1} → Arrow C := PEmpty.elim
  obtain ⟨T, _, κ, hκ, _, hω, _, hFixed, hResolution, _⟩ :=
    exists_small_cofibration_family_resolution S fixed
  exact ⟨T, κ, hκ, hω, hFixed, fun i => (hResolution i).1⟩

end CofibrationFamilyResolutionTest

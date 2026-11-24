/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.CorePullback

/-!
# Public clients for the strict core-pullback comparison

The first client obtains both conclusions without supplying source or
pullback quasicategory instances. The second transports an arbitrary
compatible cone through the inverse comparison and retains both strict
projection equations.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits

universe u

namespace MathlibExtTest.AlgebraicTopology.Quasicategory.CorePullbackTest

variable {X Y S : SSet.{u}} (p : X ⟶ S) (q : Y ⟶ S)
  [SSet.InnerFibration p] [SSet.Quasicategory S] [SSet.Quasicategory Y]

/-- The complete mathematical conclusion uses only the required base
and other-source quasicategory hypotheses. -/
theorem quasicategory_and_comparison :
    SSet.Quasicategory (pullback p q) ∧ IsIso (SSet.core.pullbackComparison p q) :=
  ⟨SSet.quasicategory_pullback_of_innerFibration p q,
    SSet.core.isIso_pullbackComparison p q⟩

/-- A compatible core-valued cone lifts to the core of the actual
pullback, with both prescribed legs preserved exactly. -/
theorem exists_core_pullback_lift {A : SSet.{u}}
    (a : A ⟶ (SSet.core X : SSet.{u})) (b : A ⟶ (SSet.core Y : SSet.{u}))
    (h : a ≫ SSet.core.map p = b ≫ SSet.core.map q) :
    ∃ l : A ⟶ (SSet.core (pullback p q) : SSet.{u}),
      l ≫ SSet.core.map (pullback.fst p q) = a ∧
      l ≫ SSet.core.map (pullback.snd p q) = b := by
  let := SSet.core.isIso_pullbackComparison p q
  let E := asIso (SSet.core.pullbackComparison p q)
  have hEfst : E.hom ≫ pullback.fst (SSet.core.map p) (SSet.core.map q) =
      SSet.core.map (pullback.fst p q) := SSet.core.pullbackComparison_fst p q
  have hEsnd : E.hom ≫ pullback.snd (SSet.core.map p) (SSet.core.map q) =
      SSet.core.map (pullback.snd p q) := SSet.core.pullbackComparison_snd p q
  refine ⟨pullback.lift a b h ≫ E.inv, ?_, ?_⟩
  · rw [← hEfst]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_fst]
  · rw [← hEsnd]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_snd]

end MathlibExtTest.AlgebraicTopology.Quasicategory.CorePullbackTest

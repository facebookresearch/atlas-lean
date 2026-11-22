/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceFibration

/-!
# Quasicategories from under-slice restriction pullbacks

This file proves the under-slice dual of Joyal's Lemma 4.11.  In Mathlib's
pullback factor order, the restriction map is the second leg, so its base
change is the first projection.  That projection is a left fibration, and the
pullback is a quasicategory when both ambient simplicial sets are.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits

universe u

namespace SSet

/-- The first projection from the under-slice restriction pullback is a left
fibration.  The second pullback leg is the restriction map. -/
theorem leftFibration_sliceUnder_restriction_pullback_fst
    {K₀ K X Y : SSet.{u}} (p : X ⟶ Y) [Quasicategory Y]
    (i : K₀ ⟶ K) [Mono i] (t : K ⟶ X) :
    LeftFibration
      (pullback.fst (sliceUnder.map X (i ≫ t) p)
        (sliceUnder.restrict Y (t ≫ p) i)) := by
  exact ⟨leftFibrations.pullback_fst _ _ LeftFibration.mem⟩

/-- The under-slice restriction pullback of a map between quasicategories is a
quasicategory. -/
theorem quasicategory_sliceUnder_restriction_pullback
    {K₀ K X Y : SSet.{u}} (p : X ⟶ Y)
    [Quasicategory X] [Quasicategory Y]
    (i : K₀ ⟶ K) [Mono i] (t : K ⟶ X) :
    Quasicategory
      (pullback (sliceUnder.map X (i ≫ t) p)
        (sliceUnder.restrict Y (t ≫ p) i)) := by
  let hlf : LeftFibration
      (pullback.fst (sliceUnder.map X (i ≫ t) p)
        (sliceUnder.restrict Y (t ≫ p) i)) :=
    leftFibration_sliceUnder_restriction_pullback_fst p i t
  let hinner : InnerFibration
      (pullback.fst (sliceUnder.map X (i ≫ t) p)
        (sliceUnder.restrict Y (t ≫ p) i)) :=
    ⟨leftFibrations_le_innerFibrations _ hlf.mem⟩
  exact @quasicategory_of_innerFibration _ _
    (pullback.fst (sliceUnder.map X (i ≫ t) p)
      (sliceUnder.restrict Y (t ≫ p) i)) hinner inferInstance

end SSet

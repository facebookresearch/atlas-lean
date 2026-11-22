/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OverPullbackSubcomplexWeak
import Mathlib.AlgebraicTopology.ModelCategory.Over

/-!
# Full original horn lifting in simplicial over categories

An original over-map is a fibration exactly when it lifts every SAME
full original horn with its arbitrary original base simplex. The base
simplex in an underlying lifting problem is constructed from the actual
bottom map and original target projection. Both original lifting
equations and the entire over-map are retained.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

variable {B : SSet.{u}} {V W : Over B}

/-- Original simplicial over fibrations are detected by every full native
horn lifting problem at every original base simplex. -/
theorem overFibration_iff_hornLifting (p : V ⟶ W) : Fibration p ↔
    ∀ (n : ℕ) (k : Fin (n + 2)) (b : (Δ[n + 1] : SSet.{u}) ⟶ B),
      HasLiftingProperty (OverSubcomplex.arrow b (horn (n + 1) k)) p := by
  constructor
  · intro hp n k b
    let _ : Fibration p := hp
    have hLift : HasLiftingProperty (horn (n + 1) k).ι p.left := inferInstance
    exact hLift.over _ _
  · intro lifts
    apply (fibrations_over_iff B p).mpr
    rw [modelCategoryQuillen.fibration_iff]
    intro A D i hi
    simp only [modelCategoryQuillen.J, CategoryTheory.MorphismProperty.iSup_iff] at hi
    obtain ⟨n, ⟨k⟩⟩ := hi
    constructor
    intro a b square
    let β : (Δ[n + 1] : SSet.{u}) ⟶ B := b ≫ W.hom
    let aOver : Over.mk ((horn (n + 1) k).ι ≫ β) ⟶ V := Over.homMk a (by
      exact (congrArg (fun g => a ≫ g) p.w).symm.trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun g => g ≫ W.hom) square.w).trans (Category.assoc _ _ _))))
    let bOver : Over.mk β ⟶ W := Over.homMk b (by rfl)
    have sq : CommSq aOver (OverSubcomplex.arrow β (horn (n + 1) k)) p bOver := by
      constructor
      apply Over.OverMorphism.ext
      exact square.w
    let _ : HasLiftingProperty (OverSubcomplex.arrow β (horn (n + 1) k)) p := lifts n k β
    exact CommSq.HasLift.mk'
      { l := sq.lift.left
        fac_left := by
          exact congrArg Over.Hom.left sq.fac_left
        fac_right := by
          exact congrArg Over.Hom.left sq.fac_right }

end SSet

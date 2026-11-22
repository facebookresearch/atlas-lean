/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.Quasicategory.CoreFibration
public import MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral

/-!
# CoreFibrationTest

Native Kan fibration clients, all horn dimensions, and inferred core fibrancy.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial

universe u

namespace SSet

open modelCategoryQuillen in
example {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p] [Quasicategory Y]
    [HasStrictEquivalenceLifting p] : modelCategoryQuillen.J.rlp (core.map p) :=
  (modelCategoryQuillen.fibration_iff _).1
    (fibration_core_map_of_hasStrictEquivalenceLifting p)

open modelCategoryQuillen in
example {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p] [Quasicategory Y]
    [HasStrictEquivalenceLifting p] : Fibration (core.map p) :=
  fibration_core_map_of_hasStrictEquivalenceLifting p

example {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p] [Quasicategory Y] :
    KanComplex (core X : SSet.{u}) := by
  let : Quasicategory X := quasicategory_of_innerFibration p
  infer_instance

example {Y : SSet.{u}} [Quasicategory Y] : KanComplex (core Y : SSet.{u}) :=
  inferInstance

-- Every original horn and its entire base simplex are retained, including n=1.
open modelCategoryQuillen in
example {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p] [Quasicategory Y]
    [HasStrictEquivalenceLifting p] (n : ℕ) (j : Fin (n + 2))
    (a : (Λ[n + 1, j] : SSet.{u}) ⟶ (core X : SSet.{u}))
    (b : (Δ[n + 1] : SSet.{u}) ⟶ (core Y : SSet.{u}))
    (hsq : a ≫ core.map p = Λ[n + 1, j].ι ≫ b) :
    ∃ σ : (Δ[n + 1] : SSet.{u}) ⟶ (core X : SSet.{u}),
      Λ[n + 1, j].ι ≫ σ = a ∧ σ ≫ core.map p = b := by
  let : Fibration (core.map p) := fibration_core_map_of_hasStrictEquivalenceLifting p
  have h : HasLiftingProperty Λ[n + 1, j].ι (core.map p) := inferInstance
  obtain ⟨σ, hσhorn, hσbase⟩ := h.sq_hasLift (CommSq.mk hsq)
  exact ⟨σ, hσhorn, hσbase⟩

end SSet

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.CompletedFiberWeakEquivalence

/-!
# Public use of the original completed-fibre comparison

The up-nerve vertex retains its positive object and denominator after collapse.
The projective application uses the whole completed category and the original
auxiliary realization at an arbitrary base point.
-/

@[expose] public section

universe u v uRing vModule

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open AlgebraicKTheory.FixedTargetExtension
open AlgebraicKTheory.FixedTargetExtension.IteratedAction
open AlgebraicKTheory.FixedTargetExtension.IteratedAction.Collapse
open scoped Simplicial CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory

namespace MathlibExtTest.KTheory.Exact.Extension.CompletedFiberWeakEquivalenceTests

section IndependentUniverses

variable {C : Type u} [Category.{v + 1} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] leftSumAction MonoidalActionCategory.diagonalAction
  denominatorLeftAction

/-- A positive Hom universe does not change the actual A,D coordinates of
an up-nerve vertex: Gamma adds A to both given row objects and keeps D. -/
theorem up_vertex_retains_positive_row_and_denominator
    (E : AlgebraicKTheory.FixedTargetExtension C X) (A D : Core C) :
    let a : SInverse (Core C) (Core C) := ⟨(A, D)⟩
    let vertex := (nerveMapCommonHomUp.{u, max u (v + 1), 0} (completedFiberFunctor E)).app
      (op ⦋0⦌) (ComposableArrows.mk₀ a)
    let row := (collapseFunctor (C := C) (X := X)).obj vertex.left
    (row.of.1.A = (A.of ⊞ E.A)) ∧ (row.of.1.B = (A.of ⊞ E.B)) ∧ row.of.2 = D := by
  let a : SInverse (Core C) (Core C) := ⟨(A, D)⟩
  let vertex := (nerveMapCommonHomUp.{u, max u (v + 1), 0} (completedFiberFunctor E)).app
    (op ⦋0⦌) (ComposableArrows.mk₀ a)
  have hVertex : vertex.left = (completedFiberFunctor E).obj a := by
    exact congrArg
      (fun z : ComposableArrows (Collapse.iteratedLocalizedRows (C := C) (X := X)) 0 => z.left)
      (nerveMapCommonHomUp_app_mk₀ (completedFiberFunctor E) a)
  have hRow : ((collapseFunctor (C := C) (X := X)).obj vertex.left).of =
      (leftSumObj A E, D) :=
    (congrArg
      (fun n : Collapse.iteratedLocalizedRows (C := C) (X := X) =>
        ((collapseFunctor (C := C) (X := X)).obj n).of) hVertex).trans
      (collapse_completedFiber_object E a)
  exact ⟨congrArg
    (fun p : AlgebraicKTheory.FixedTargetExtension C X × Core C => p.1.A) hRow,
    congrArg (fun p : AlgebraicKTheory.FixedTargetExtension C X × Core C => p.1.B) hRow,
    congrArg (fun p : AlgebraicKTheory.FixedTargetExtension C X × Core C => p.2) hRow⟩

end IndependentUniverses

section AllRings

attribute [local instance] leftSumAction MonoidalActionCategory.diagonalAction
  denominatorLeftAction

/-- The original all-ring J map and a real homotopy-fibre projection can be
used together, with no supplied weakness or selected-zero-component input. -/
theorem allRing_completed_map_and_original_auxiliary_fiber
    {R : Type uRing} [Ring R] (X : FGProjectiveCat.{vModule} R)
    (E : AlgebraicKTheory.FixedTargetExtension (FGProjectiveCat.{vModule} R) X)
    (T : TopCat.{max uRing (vModule + 1)})
    (p : T ⟶ SSet.toTop.obj
      (nerve (AlgebraicKTheory.AuxiliaryExtension.Auxiliary
        (FGProjectiveCat.{vModule} R) X)))
    (b : SSet.toTop.obj
      (nerve (AlgebraicKTheory.AuxiliaryExtension.Auxiliary
        (FGProjectiveCat.{vModule} R) X))) :
    SSet.realizationWeakEquivalences (nerveMapCommonHomUp.{max uRing (vModule + 1), max uRing
      (vModule + 1), 0} (completedFiberFunctor E)) ∧
      TopCat.weakHomotopyEquivalences (TopCat.homotopyFiberToTotal p b) := by
  refine ⟨projectiveCompletedFiberNerveMap_mem_realizationWeakEquivalences X E, ?_⟩
  exact TopCat.homotopyFiberToTotal_mem_of_base_conull p b
    (AlgebraicKTheory.AuxiliaryExtension.projectiveAuxiliary_realization_conull X)

end AllRings

#print axioms up_vertex_retains_positive_row_and_denominator
#print axioms allRing_completed_map_and_original_auxiliary_fiber

end MathlibExtTest.KTheory.Exact.Extension.CompletedFiberWeakEquivalenceTests

end

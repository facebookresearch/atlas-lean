/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryBar.QuillenTheoremARight
import Mathlib.CategoryTheory.Adjunction.Comma
import Mathlib.CategoryTheory.Category.GaloisConnection
public import Mathlib.CategoryTheory.SingleObj
import Mathlib.Algebra.Group.ULift

/-!
# Public right-comma Quillen-A consumers

The tests derive their comparison maps and weak equivalences from actual
adjunctions. They distinguish the two comma directions in Fin2, retain
parallel morphisms, and exercise arbitrary object and Hom universes through
the down functor. The concrete corner has Type0 objects and Type1 morphisms,
so both native nerves lie in SSet1.
-/

universe u v

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace MathlibExtTest.QuillenARight

/-- Arbitrary categories: a left adjoint has actual terminal right commas. -/
theorem left_adjoint_right_comma
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F : C ⥤ D} (G : D ⥤ C) (h : F ⊣ G) :
    SSet.realizationWeakEquivalences (nerveMap F) := by
  apply SSet.OppositeRealization.nerveMap_mem_of_costructuredArrow F
  intro d
  exact NerveContractible.nerve_to_terminal_mem_realizationWeakEquivalences_of_isTerminal
    (mkTerminalOfRightAdjoint G h d)

/-- The public criterion works without identifying two parallel generators. -/
theorem parallel_morphisms_survive :
    WalkingParallelPairHom.left ≠ WalkingParallelPairHom.right ∧
      SSet.realizationWeakEquivalences (nerveMap (𝟭 WalkingParallelPair)) := by
  constructor
  · decide
  · exact left_adjoint_right_comma (𝟭 WalkingParallelPair) Adjunction.id

private theorem initialPointGC :
    GaloisConnection (fun _ : Fin 1 => (0 : Fin 2))
      (fun _ : Fin 2 => (0 : Fin 1)) := by
  intro a b
  simp

/-- The literal public constant-zero functor satisfies the right-comma criterion. -/
theorem initial_point_right_comma :
    SSet.realizationWeakEquivalences
      (nerveMap ((Functor.const (Fin 1)).obj (0 : Fin 2))) := by
  have hL : initialPointGC.monotone_l.functor =
      (Functor.const (Fin 1)).obj (0 : Fin 2) := by
    exact CategoryTheory.Functor.ext
      (fun _ => rfl)
      (fun _ _ _ => Subsingleton.elim _ _)
  have hAdj : (Functor.const (Fin 1)).obj (0 : Fin 2) ⊣
      initialPointGC.monotone_u.functor :=
    hL ▸ GaloisConnection.adjunction initialPointGC
  exact left_adjoint_right_comma initialPointGC.monotone_u.functor hAdj

/-- At the opposite endpoint the right comma is empty while the left comma has an object. -/
theorem right_left_comma_are_different :
    IsEmpty (CostructuredArrow ((Functor.const (Fin 1)).obj (1 : Fin 2)) (0 : Fin 2)) ∧
      Nonempty (StructuredArrow (0 : Fin 2) ((Functor.const (Fin 1)).obj (1 : Fin 2))) := by
  constructor
  · constructor
    intro a
    have h : (1 : Fin 2) ≤ 0 := leOfHom a.hom
    exact (by decide : ¬ ((1 : Fin 2) ≤ 0)) h
  · exact ⟨StructuredArrow.mk (Y := (0 : Fin 1)) (homOfLE (by decide))⟩

/-- The ordinary opposite-comma functor reverses every actual structural arrow. -/
theorem opposite_arrow_has_correct_direction
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (d : D) (a : CostructuredArrow F d) :
    ((CostructuredArrow.toStructuredArrow F d).obj (op a)).hom = a.hom.op := rfl

section CrossUniverse

attribute [local instance] CategoryTheory.uliftCategory

/-- Arbitrary B object-u/Hom-v: right commas of the actual down functor are terminal. -/
theorem arbitrary_cross_down {B : Type u} [Category.{v} B] :
    SSet.realizationWeakEquivalences
      (nerveMapCross (ULift.downFunctor : ULift.{v} B ⥤ B)) := by
  apply SSet.OppositeRealization.crossMap_mem_of_costructuredArrow
    (ULift.downFunctor : ULift.{v} B ⥤ B)
  intro b
  exact NerveContractible.nerve_to_terminal_mem_realizationWeakEquivalences_of_isTerminal
    (mkTerminalOfRightAdjoint (ULift.upFunctor : B ⥤ ULift.{v} B)
      (ULift.equivalence (C := B) : B ≌ ULift.{v} B).symm.toAdjunction b)

/-- The stock one-object monoid category has object-Type0 and Hom-Type1. -/
theorem distinct_object_Hom_corner :
    SSet.realizationWeakEquivalences
      (nerveMapCross.{1, 0}
        (ULift.downFunctor :
          ULift.{1, 0} (SingleObj (ULift.{1, 0} PUnit.{1})) ⥤
            SingleObj (ULift.{1, 0} PUnit.{1})) :
        (nerve (ULift.{1, 0} (SingleObj (ULift.{1, 0} PUnit.{1}))) : SSet.{1}) ⟶
          (nerve (SingleObj (ULift.{1, 0} PUnit.{1})) : SSet.{1})) :=
  arbitrary_cross_down.{0, 1} (B := SingleObj (ULift.{1, 0} PUnit.{1}))

end CrossUniverse

/-! ## The right-comma hypothesis cannot be replaced by the other variance. -/

section NegativeDirection

variable {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D)

/-- error: Application type mismatch -/
#guard_msgs (error, substring := true) in
example (hWrong : ∀ d : D, SSet.realizationWeakEquivalences
    (terminal.from (nerve (StructuredArrow d F)))) :
    SSet.realizationWeakEquivalences (nerveMap F) :=
  SSet.OppositeRealization.nerveMap_mem_of_costructuredArrow F hWrong

end NegativeDirection

/-! ## Axiom assertions for the meaningful generic clients. -/

/--
info: 'MathlibExtTest.QuillenARight.left_adjoint_right_comma'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MathlibExtTest.QuillenARight.left_adjoint_right_comma

/--
info: 'MathlibExtTest.QuillenARight.arbitrary_cross_down'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MathlibExtTest.QuillenARight.arbitrary_cross_down

end MathlibExtTest.QuillenARight

end

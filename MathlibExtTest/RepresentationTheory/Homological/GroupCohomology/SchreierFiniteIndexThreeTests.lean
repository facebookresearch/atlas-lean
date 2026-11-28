/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferDegreeThree
import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferNorm
import
  MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferArbitraryNaturality
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic
meta import Mathlib.Tactic.NormNum

/-!
# Proper finite-index transfer and independent quotient universes

The order-three group maps isomorphically to its universe-lifted copy. Its kernel is a proper
subgroup, and the canonical right transversal has three elements. Integer cochain transfer
therefore sends the constant cochain two to six in every degree, including degree three.
The coefficient map multiplication by five sends that value to thirty. For the same trivial
action on the multiplicative copy of the integers, the transversal norm of two is six.
The degree-three cochain calculation concerns raw cochains, with their actual coefficient
module and representative scan.
-/

open CategoryTheory groupCohomology
open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace SchreierFiniteIndexThreeTests

private abbrev G := Multiplicative (ZMod 3)
private abbrev Q := ULift.{1} G

private abbrev liftHom : G →* Q where
  toFun := ULift.up
  map_one' := rfl
  map_mul' _ _ := rfl

private lemma lift_surjective : Function.Surjective liftHom := fun q => ⟨q.down, rfl⟩
private abbrev H := liftHom.ker
private def T : H.RightTransversal := default

private instance : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

private def quotientCoordinate : Q ≃ ZMod 3 where
  toFun q := q.down.toAdd
  invFun x := ULift.up (Multiplicative.ofAdd x)
  left_inv _ := rfl
  right_inv _ := rfl

private lemma transversal_card : Fintype.card (T : Set G) = 3 :=
  (Fintype.card_congr (rightTransversalEquivCodomain liftHom lift_surjective T)).trans
    ((Fintype.card_congr quotientCoordinate).trans (by decide))

example : H ≠ ⊤ := by
  intro h
  let s : G := Multiplicative.ofAdd (1 : ZMod 3)
  have hs : s ∈ H := by rw [h]; trivial
  change ULift.up s = ULift.up (1 : G) at hs
  have he : s = 1 := congrArg ULift.down hs
  exact (by decide : s ≠ 1) he

example : Fintype.card (T : Set G) = 3 := transversal_card

private abbrev A : Rep ℤ G := Rep.trivial ℤ G ℤ

private lemma transfer_value (n : ℕ) (g : Fin n → G) :
    corestrictionCochain A T n (fun _ => (2 : ℤ)) g = 6 := by
  rw [corestrictionCochain_apply]
  simp only [Rep.trivial_ρ_apply]
  rw [Finset.sum_const, Finset.card_univ, transversal_card]
  norm_num

example : corestrictionCochain A T 0 (fun _ => (2 : ℤ)) (fun i => i.elim0) = 6 :=
  transfer_value 0 _

example : corestrictionCochain A T 3 (fun _ => (2 : ℤ)) (fun _ => 1) = 6 :=
  transfer_value 3 _

example : corestrictionCochain A T 3 (fun _ => (2 : ℤ)) ≠ 0 := by
  intro h
  have he := congrFun h (fun _ => (1 : G))
  rw [transfer_value] at he
  exact (by norm_num : (6 : ℤ) ≠ 0) he

example : corestrictionCochainThree A T (fun _ => (2 : ℤ)) (1, 1, 1) = 6 := by
  rw [corestrictionCochainThree_apply]
  simp only [Rep.trivial_ρ_apply]
  rw [Finset.sum_const, Finset.card_univ, transversal_card]
  norm_num

private abbrev five : A ⟶ A := Rep.ofHom ⟨(5 : ℤ) • LinearMap.id, fun _ => rfl⟩

example : corestrictionCochain A T 3 (fun _ => five.hom (2 : ℤ)) (fun _ => 1) = 30 := by
  have h := congrFun (corestrictionCochain_naturality five T 3 (fun _ => (2 : ℤ)))
    (fun _ => (1 : G))
  rw [transfer_value] at h
  exact h.symm.trans (by rfl)

private abbrev M := Multiplicative ℤ

private instance : MulDistribMulAction G M where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

private lemma trivial_action (g : G) (x : M) : g • x = x := rfl

example : rightTransversalNorm T (Multiplicative.ofAdd (2 : ℤ)) =
    Multiplicative.ofAdd (6 : ℤ) := by
  rw [rightTransversalNorm_apply]
  simp only [trivial_action]
  rw [Finset.prod_const, Finset.card_univ, transversal_card]
  rfl

end SchreierFiniteIndexThreeTests

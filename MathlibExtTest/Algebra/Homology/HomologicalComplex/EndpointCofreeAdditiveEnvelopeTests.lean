/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Homology.HomologicalComplex.EndpointCofreeAdjunction
import Mathlib.CategoryTheory.Preadditive.Mat
import Mathlib.Data.ZMod.Basic

/-!
# Cofree complexes in the additive envelope of the integers

Finite tuples in the single-object category of the integer ring model finite
free integer modules. This category has zero objects and finite biproducts;
it has no supplied abelian structure. The cofree construction and adjunction
apply to a cyclic shape, and its nonzero differential is detected by the
single integer matrix coefficient after the two canonical projections.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace MathlibExtTest.EndpointCofreeAdditiveEnvelope

private abbrev C := Mat_ (SingleObj ℤ)
private instance : HasBinaryBiproducts C := hasBinaryBiproducts_of_finite_biproducts C
private abbrev N : C where
  ι := Fin 1
  X _ := PUnit.unit
private abbrev c := ComplexShape.down (ZMod 2)
private abbrev I : GradedObject (ZMod 2) C := fun _ => N
private abbrev D : HomologicalComplex C c := endpointCofree c I
private lemma rel_zero_one : c.Rel 0 1 := by decide

example : HasZeroObject C := inferInstance
example : HasBinaryBiproducts C := inferInstance
example : forget C c ⊣ endpointCofreeFunctor C c := endpointCofreeAdjunction C c
example : (endpointCofreeFunctor C c).IsRightAdjoint := inferInstance

private def detected : N ⟶ N :=
  (endpointCofreeNextTermIso I rel_zero_one).inv ≫
    (biprod.inr : endpointCofreeNextTerm c I 0 ⟶ D.X 0) ≫
      D.d 0 1 ≫ endpointCofreeProjection c I 1

private lemma detected_eq : detected = 𝟙 N := by
  rw [detected, endpointCofree_d I rel_zero_one]
  change (endpointCofreeNextTermIso I rel_zero_one).inv ≫
    (biprod.inr : endpointCofreeNextTerm c I 0 ⟶
      I 0 ⊞ endpointCofreeNextTerm c I 0) ≫
    ((biprod.snd : I 0 ⊞ endpointCofreeNextTerm c I 0 ⟶
      endpointCofreeNextTerm c I 0) ≫
      (endpointCofreeNextTermIso I rel_zero_one).hom ≫ biprod.inl) ≫
    (biprod.fst : I 1 ⊞ endpointCofreeNextTerm c I 1 ⟶ I 1) = 𝟙 N
  simp only [endpointCofreeSecondProjection, endpointCofreeInclusion,
    endpointCofreeProjection, Category.assoc, biprod.inr_snd_assoc,
    biprod.inl_fst, Category.comp_id, Iso.inv_hom_id]

example : detected (0 : Fin 1) (0 : Fin 1) = (1 : ℤ) := by
  rw [detected_eq, Mat_.id_apply_self]
  rfl

example : D.d 0 1 ≠ 0 := by
  intro hz
  have hzero : detected = 0 := by
    rw [detected, hz]
    erw [Limits.zero_comp, Limits.comp_zero, Limits.comp_zero]
  have h := congrArg (fun f : N ⟶ N => f (0 : Fin 1) (0 : Fin 1))
    (detected_eq.symm.trans hzero)
  rw [Mat_.id_apply_self] at h
  change (1 : ℤ) = 0 at h
  exact (by decide : (1 : ℤ) ≠ 0) h

example : D.d 0 1 ≫ D.d 1 0 = 0 := D.d_comp_d 0 1 0

end MathlibExtTest.EndpointCofreeAdditiveEnvelope

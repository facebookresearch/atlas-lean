/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Objects killed by an integer

An integer kills an object when it kills that object's identity morphism.
Additive functors preserve the condition and faithful additive functors
reflect it. The condition transports through object isomorphisms and
controls signs on morphisms involving an object killed by two.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D]

/-- An object is killed by `m` when its identity is killed by `m`. -/
def IsKilledBy (A : C) (m : ℕ) : Prop := m • (𝟙 A : A ⟶ A) = 0

/-- Every arrow from an object killed by `m` is killed by `m`. -/
theorem IsKilledBy.nsmul_hom_source {A B : C} {m : ℕ} (hA : IsKilledBy A m)
    (f : A ⟶ B) : m • f = 0 := by
  have h := congrArg (fun t : A ⟶ A => t ≫ f) hA
  simpa only [nsmul_comp, Category.id_comp, zero_comp] using h

/-- Every arrow into an object killed by `m` is killed by `m`. -/
theorem IsKilledBy.nsmul_hom_target {A B : C} {m : ℕ} (hB : IsKilledBy B m)
    (f : A ⟶ B) : m • f = 0 := by
  have h := congrArg (fun t : B ⟶ B => f ≫ t) hB
  simpa only [comp_nsmul, Category.comp_id, comp_zero] using h

/-- Additive functors preserve the object condition. -/
theorem IsKilledBy.map {A : C} {m : ℕ} (hA : IsKilledBy A m)
    (F : C ⥤ D) [F.Additive] : IsKilledBy (F.obj A) m := by
  have h := congrArg (fun t : A ⟶ A => F.map t) hA
  simpa only [IsKilledBy, Functor.map_nsmul, Functor.map_id, Functor.map_zero] using h

/-- A faithful additive functor reflects the object condition. -/
theorem isKilledBy_of_faithful_map (F : C ⥤ D) [F.Additive] [F.Faithful]
    (A : C) (m : ℕ) (hA : IsKilledBy (F.obj A) m) : IsKilledBy A m := by
  apply F.map_injective
  simpa only [IsKilledBy, Functor.map_nsmul, Functor.map_id, Functor.map_zero] using hA

/-- The condition transfers through the given object isomorphism. -/
theorem IsKilledBy.of_iso {A B : C} {m : ℕ} (hA : IsKilledBy A m)
    (e : A ≅ B) : IsKilledBy B m := by
  have h := congrArg (fun t : A ⟶ A => e.inv ≫ t ≫ e.hom) hA
  simpa only [IsKilledBy, comp_nsmul, nsmul_comp, Category.id_comp, Iso.inv_hom_id,
    comp_zero, zero_comp] using h

/-- Quotients of an object killed by `m` are killed by `m`. -/
theorem IsKilledBy.of_epi {A B : C} {m : ℕ} (hA : IsKilledBy A m)
    (f : A ⟶ B) [Epi f] : IsKilledBy B m := by
  apply (cancel_epi f).mp
  simpa only [comp_nsmul, Category.comp_id, comp_zero] using hA.nsmul_hom_source f

/-- Subobjects of an object killed by `m` are killed by `m`. -/
theorem IsKilledBy.of_mono {A B : C} {m : ℕ} (hB : IsKilledBy B m)
    (f : A ⟶ B) [Mono f] : IsKilledBy A m := by
  apply (cancel_mono f).mp
  simpa only [nsmul_comp, Category.id_comp, zero_comp] using hB.nsmul_hom_target f

/-- Negation is the identity on arrows from an object killed by two. -/
theorem IsKilledBy.neg_hom_source {A B : C} (hA : IsKilledBy A 2)
    (f : A ⟶ B) : -f = f := by
  apply neg_eq_iff_add_eq_zero.mpr
  simpa only [two_nsmul] using hA.nsmul_hom_source f

/-- Negation is the identity on arrows into an object killed by two. -/
theorem IsKilledBy.neg_hom_target {A B : C} (hB : IsKilledBy B 2)
    (f : A ⟶ B) : -f = f := by
  apply neg_eq_iff_add_eq_zero.mpr
  simpa only [two_nsmul] using hB.nsmul_hom_target f

/-- Every integer sign acts trivially on an arrow from an two-torsion object. -/
theorem IsKilledBy.neg_one_pow_zsmul_hom_source {A B : C} (hA : IsKilledBy A 2)
    (f : A ⟶ B) (n : ℕ) : ((-1 : ℤ) ^ n) • f = f := by
  induction n with
  | zero => simp only [pow_zero, one_zsmul]
  | succ n ih =>
    rw [pow_succ, mul_smul, neg_one_zsmul, smul_neg, ih]
    exact hA.neg_hom_source f

/-- Every integer sign acts trivially on an arrow into an two-torsion object. -/
theorem IsKilledBy.neg_one_pow_zsmul_hom_target {A B : C} (hB : IsKilledBy B 2)
    (f : A ⟶ B) (n : ℕ) : ((-1 : ℤ) ^ n) • f = f := by
  induction n with
  | zero => simp only [pow_zero, one_zsmul]
  | succ n ih =>
    rw [pow_succ, mul_smul, neg_one_zsmul, smul_neg, ih]
    exact hB.neg_hom_target f

end CategoryTheory.Preadditive

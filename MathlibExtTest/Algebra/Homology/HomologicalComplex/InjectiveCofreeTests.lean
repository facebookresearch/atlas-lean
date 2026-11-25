/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.FinCases
public import MathlibExt.Algebra.Homology.HomologicalComplex.InjectiveCofree

/-!
# Cofree embeddings of a periodic torsion complex

The two-periodic complex of integer modules has coefficient module
`ULift (ZMod 6)` and alternating differentials ×2 and ×3. Both differentials
are nonzero and their composites vanish. Native injective covers give a
monic embedding into the finite cofree complex. Its second coefficients
retain the two differential values through the injective cover.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Classical

namespace InjectiveCofreeTests

private abbrev A := ModuleCat.{1} ℤ
private abbrev V := ULift.{1} (ZMod 6)
private abbrev N : A := ModuleCat.of ℤ V
private abbrev c := ComplexShape.down (ZMod 2)

private lemma rel_zero_one : c.Rel 0 1 := by decide
private lemma rel_one_zero : c.Rel 1 0 := by decide

private lemma next_zero : c.next 0 = 1 := c.next_eq' rel_zero_one
private lemma next_one : c.next 1 = 0 := c.next_eq' rel_one_zero

private lemma rel_next (i : ZMod 2) : c.Rel i (c.next i) := by
  have h : c.Rel i (i - 1) := by
    change i - 1 + 1 = i
    exact sub_add_cancel i 1
  simpa only [c.next_eq' h] using h

private lemma six_smul (x : V) : (6 : ℤ) • x = 0 := by
  apply ULift.ext
  change (6 : ℤ) • x.down = 0
  rw [zsmul_eq_mul, show (6 : ZMod 6) = 0 by decide, zero_mul]

private lemma two_three : ((2 : ℤ) • 𝟙 N) ≫ ((3 : ℤ) • 𝟙 N) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (3 : ℤ) • ((2 : ℤ) • x) = 0
  rw [smul_smul]
  exact six_smul x

private lemma three_two : ((3 : ℤ) • 𝟙 N) ≫ ((2 : ℤ) • 𝟙 N) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (2 : ℤ) • ((3 : ℤ) • x) = 0
  rw [smul_smul]
  exact six_smul x

private abbrev step (i : ZMod 2) : N ⟶ N :=
  if i = 0 then (2 : ℤ) • 𝟙 N else (3 : ℤ) • 𝟙 N

private lemma step_square {i j : ZMod 2} (hij : c.Rel i j) : step i ≫ step j = 0 := by
  fin_cases i <;> fin_cases j
  · exact False.elim ((by decide : ¬ c.Rel 0 0) hij)
  · simpa only [step, if_pos rfl, if_neg (by decide : (1 : ZMod 2) ≠ 0)]
      using two_three
  · simpa only [step, if_pos rfl, if_neg (by decide : (1 : ZMod 2) ≠ 0)]
      using three_two
  · exact False.elim ((by decide : ¬ c.Rel 1 1) hij)

private abbrev K : HomologicalComplex A c where
  X _ := N
  d i j := if c.Rel i j then step i else 0
  shape i j hij := by simp only [if_neg hij]
  d_comp_d' i j k hij hjk := by
    simp only [if_pos hij, if_pos hjk]
    exact step_square hij

private lemma d_zero_one : (K.d 0 1).hom (ULift.up 1) = ULift.up (2 : ZMod 6) := by
  change (if c.Rel 0 1 then step 0 else 0).hom (ULift.up 1) = _
  rw [if_pos rel_zero_one]
  change (2 : ℤ) • (ULift.up (1 : ZMod 6) : V) = ULift.up (2 : ZMod 6)
  apply ULift.ext
  decide

private lemma d_one_zero : (K.d 1 0).hom (ULift.up 1) = ULift.up (3 : ZMod 6) := by
  change (if c.Rel 1 0 then step 1 else 0).hom (ULift.up 1) = _
  rw [if_pos rel_one_zero]
  simp only [step, if_neg (by decide : (1 : ZMod 2) ≠ 0)]
  change (3 : ℤ) • (ULift.up (1 : ZMod 6) : V) = ULift.up (3 : ZMod 6)
  apply ULift.ext
  decide

private abbrev J : A := Injective.under N
private abbrev I : ZMod 2 → A := fun _ => J
private abbrev a : ∀ i : ZMod 2, K.X i ⟶ I i := fun _ => Injective.ι N
private abbrev D : HomologicalComplex A c := HomologicalComplex.injectiveCofree (c := c) I
private abbrev embedding : K ⟶ D := HomologicalComplex.injectiveCofreeHom K I a

private instance coefficient_injective : ∀ i, Injective (I i) :=
  fun _ => by change Injective J; infer_instance

private instance coefficient_mono : ∀ i, Mono (a i) :=
  fun _ => by change Mono (Injective.ι N); infer_instance

private lemma cover_ne_zero {x : ZMod 6} (hx : x ≠ 0) :
    (Injective.ι N).hom (ULift.up x) ≠ 0 := by
  intro hzero
  have hι := (ModuleCat.mono_iff_injective (Injective.ι N)).mp inferInstance
  have h := hι (hzero.trans ((Injective.ι N).hom.map_zero).symm)
  exact hx (congrArg ULift.down h)

private lemma embedding_snd_zero :
    (embedding.f 0 ≫ (biprod.snd : J ⊞ J ⟶ J)).hom (ULift.up 1) =
      (Injective.ι N).hom (ULift.up (2 : ZMod 6)) := by
  have h := HomologicalComplex.injectiveCofreeHom_snd K I a (0 : ZMod 2)
  rw [next_zero] at h
  rw [h]
  change (Injective.ι N).hom ((K.d 0 1).hom (ULift.up 1)) = _
  rw [d_zero_one]

private lemma embedding_snd_one :
    (embedding.f 1 ≫ (biprod.snd : J ⊞ J ⟶ J)).hom (ULift.up 1) =
      (Injective.ι N).hom (ULift.up (3 : ZMod 6)) := by
  have h := HomologicalComplex.injectiveCofreeHom_snd K I a (1 : ZMod 2)
  rw [next_one] at h
  rw [h]
  change (Injective.ι N).hom ((K.d 1 0).hom (ULift.up 1)) = _
  rw [d_one_zero]

example : K.d 0 1 ≠ 0 ∧ K.d 1 0 ≠ 0 := by
  constructor
  · intro h
    have hx := d_zero_one
    rw [h] at hx
    have he := congrArg ULift.down hx
    exact (by decide : (0 : ZMod 6) ≠ 2) he
  · intro h
    have hx := d_one_zero
    rw [h] at hx
    have he := congrArg ULift.down hx
    exact (by decide : (0 : ZMod 6) ≠ 3) he

example : K.d 0 1 ≫ K.d 1 0 = 0 ∧ K.d 1 0 ≫ K.d 0 1 = 0 :=
  ⟨K.d_comp_d 0 1 0, K.d_comp_d 1 0 1⟩

example : EnoughInjectives (HomologicalComplex A c) :=
  HomologicalComplex.enoughInjectives_of_rel_next rel_next

example : Injective D := HomologicalComplex.injectiveCofree_injective I rel_next

example : Mono embedding := HomologicalComplex.injectiveCofreeHom_mono K I a

example : (embedding.f 0 ≫ (biprod.fst : J ⊞ J ⟶ J)).hom (ULift.up 1) ≠ 0 := by
  rw [HomologicalComplex.injectiveCofreeHom_fst]
  exact cover_ne_zero (by decide : (1 : ZMod 6) ≠ 0)

example : (embedding.f 0 ≫ (biprod.snd : J ⊞ J ⟶ J)).hom (ULift.up 1) =
    (Injective.ι N).hom (ULift.up (2 : ZMod 6)) := embedding_snd_zero

example : (embedding.f 1 ≫ (biprod.snd : J ⊞ J ⟶ J)).hom (ULift.up 1) =
    (Injective.ι N).hom (ULift.up (3 : ZMod 6)) := embedding_snd_one

example : (embedding.f 0 ≫ (biprod.snd : J ⊞ J ⟶ J)).hom (ULift.up 1) ≠ 0 ∧
    (embedding.f 1 ≫ (biprod.snd : J ⊞ J ⟶ J)).hom (ULift.up 1) ≠ 0 := by
  rw [embedding_snd_zero, embedding_snd_one]
  exact ⟨cover_ne_zero (by decide : (2 : ZMod 6) ≠ 0),
    cover_ne_zero (by decide : (3 : ZMod 6) ≠ 0)⟩

example : (biprod.inr : J ⟶ J ⊞ J) ≫ D.d 0 1 ≫
    (biprod.fst : J ⊞ J ⟶ J) = 𝟙 J := by
  rw [HomologicalComplex.injectiveCofree_d I rel_zero_one]
  simp only [eqToHom_refl, Category.assoc, Category.id_comp,
    biprod.inl_fst, Category.comp_id, biprod.inr_snd]

private abbrev coefficientDouble : ∀ i : ZMod 2, I i ⟶ I i :=
  fun _ => (2 : ℤ) • 𝟙 J

example : embedding ≫ HomologicalComplex.injectiveCofreeMap (c := c) coefficientDouble =
    HomologicalComplex.injectiveCofreeHom K I (fun i => a i ≫ coefficientDouble i) :=
  HomologicalComplex.injectiveCofreeHom_naturality K rel_next a coefficientDouble

end InjectiveCofreeTests

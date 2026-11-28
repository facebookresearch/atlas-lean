/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Codex
-/

module

import MathlibExt.Algebra.Homology.HomologicalComplex.EndpointCofree
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Module.ULift
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
public meta import Lean.Elab.Tactic.Omega

/-!
# Nonzero endpoint and cyclic cofree embeddings

Work in ModuleCat.{1} ℤ with coefficient ULift.{1}(ℤ/6). A chain complex
indexed by ℕ has alternating differentials given by multiplication by two
and three. Their composites vanish because six acts by zero, while the
individual differential values are nonzero.

Degree zero has no outgoing differential, so its cofree term has zero
second coefficient and identifies with its first injective coefficient.
Along outgoing edges, the cofree second components retain the nonzero
differential values through the chosen injective inclusions. Doubling the
injective coefficients also gives a nonzero value at the endpoint.

A second complex has the cyclic shape indexed by ℤ/2, with multiplication
by two in one direction and by three in the other. Both second coefficients
are nonzero. The coefficient objects throughout are the chosen injective
objects containing the lifted module.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Classical ZeroObject

namespace MathlibExtTest.EndpointCofree

private abbrev A := ModuleCat.{1} ℤ
private abbrev V := ULift.{1} (ZMod 6)
private abbrev N : A := ModuleCat.of ℤ V
private abbrev J : A := Injective.under N

private lemma six_smul (x : V) : (6 : ℤ) • x = 0 := by
  apply ULift.ext
  change (6 : ℤ) • x.down = 0
  simp [zsmul_eq_mul, show (6 : ZMod 6) = 0 from by decide]

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

private lemma two_one :
    (2 : ℤ) • (ULift.up (1 : ZMod 6) : V) = ULift.up (2 : ZMod 6) := by
  apply ULift.ext
  decide

private lemma cover_ne_zero {x : ZMod 6} (hx : x ≠ 0) :
    (Injective.ι N).hom (ULift.up x) ≠ 0 := by
  intro hzero
  have hι := (ModuleCat.mono_iff_injective (Injective.ι N)).mp inferInstance
  have h := hι (hzero.trans ((Injective.ι N).hom.map_zero).symm)
  exact hx (congrArg ULift.down h)

namespace NatBoundary

private abbrev c := ComplexShape.down ℕ

private abbrev step (n : ℕ) : N ⟶ N :=
  if n % 2 = 0 then (2 : ℤ) • 𝟙 N else (3 : ℤ) • 𝟙 N

private lemma step_square (n : ℕ) : step (n + 1) ≫ step n = 0 := by
  by_cases h : n % 2 = 0
  · have hn : (n + 1) % 2 ≠ 0 := by omega
    simpa only [step, if_pos h, if_neg hn] using three_two
  · have hn : (n + 1) % 2 = 0 := by omega
    simpa only [step, if_neg h, if_pos hn] using two_three

private abbrev K : ChainComplex A ℕ where
  X _ := N
  d i j := if c.Rel i j then step j else 0
  shape i j hij := by simp only [if_neg hij]
  d_comp_d' i j k hij hjk := by
    have h : k + 1 = j := hjk
    simp only [if_pos hij, if_pos hjk]
    rw [← h]
    exact step_square k

private lemma no_next_zero : ¬ c.Rel 0 (c.next 0) := by
  intro h
  change c.next 0 + 1 = 0 at h
  omega

private lemma rel_one_zero : c.Rel 1 0 := by decide
private lemma rel_two_one : c.Rel 2 1 := by decide

private abbrev I : ℕ → A := fun _ => J
private abbrev a : ∀ i : ℕ, K.X i ⟶ I i := fun _ => Injective.ι N
private abbrev D : ChainComplex A ℕ := endpointCofree (c := c) I
private abbrev embedding : K ⟶ D := endpointCofreeHom K I a

private instance coefficient_injective : ∀ i, Injective (I i) :=
  fun _ => by change Injective J; infer_instance

private instance coefficient_mono : ∀ i, Mono (a i) :=
  fun _ => by change Mono (Injective.ι N); infer_instance

private lemma d_one_zero : (K.d 1 0).hom (ULift.up 1) = ULift.up (2 : ZMod 6) := by
  change (if c.Rel 1 0 then step 0 else 0).hom (ULift.up 1) = _
  rw [if_pos rel_one_zero]
  change (2 : ℤ) • (ULift.up (1 : ZMod 6) : V) = ULift.up (2 : ZMod 6)
  exact two_one

private lemma d_two_one : (K.d 2 1).hom (ULift.up 1) = ULift.up (3 : ZMod 6) := by
  change (if c.Rel 2 1 then step 1 else 0).hom (ULift.up 1) = _
  rw [if_pos rel_two_one]
  simp only [step, if_neg (by decide : ¬ (1 : ℕ) % 2 = 0)]
  change (3 : ℤ) • (ULift.up (1 : ZMod 6) : V) = ULift.up (3 : ZMod 6)
  apply ULift.ext
  decide

private lemma embedding_second_one :
    ((embedding.f 1 ≫ endpointCofreeSecondProjection (c := c) I 1) ≫
      (endpointCofreeNextTermIso I rel_one_zero).hom).hom (ULift.up 1) =
        (Injective.ι N).hom (ULift.up (2 : ZMod 6)) := by
  rw [endpointCofreeHom_snd_of_rel K I a rel_one_zero]
  change (Injective.ι N).hom ((K.d 1 0).hom (ULift.up 1)) = _
  rw [d_one_zero]

private lemma embedding_second_two :
    ((embedding.f 2 ≫ endpointCofreeSecondProjection (c := c) I 2) ≫
      (endpointCofreeNextTermIso I rel_two_one).hom).hom (ULift.up 1) =
        (Injective.ι N).hom (ULift.up (3 : ZMod 6)) := by
  rw [endpointCofreeHom_snd_of_rel K I a rel_two_one]
  change (Injective.ι N).hom ((K.d 2 1).hom (ULift.up 1)) = _
  rw [d_two_one]

example : endpointCofreeNextTerm (c := c) I 0 = (0 : A) :=
  endpointCofreeNextTerm_of_no_next I 0 no_next_zero

example : D.X 0 ≅ J :=
  endpointCofreeXIsoOfNoNext I 0 no_next_zero

example : D.d 0 0 = 0 :=
  D.shape 0 0 (by decide)

example : K.d 1 0 ≠ 0 ∧ K.d 2 1 ≠ 0 := by
  constructor
  · intro h
    have hx := d_one_zero
    rw [h] at hx
    exact (by decide : (0 : ZMod 6) ≠ 2) (congrArg ULift.down hx)
  · intro h
    have hx := d_two_one
    rw [h] at hx
    exact (by decide : (0 : ZMod 6) ≠ 3) (congrArg ULift.down hx)

example : K.d 2 1 ≫ K.d 1 0 = 0 := K.d_comp_d 2 1 0

example : EnoughInjectives (HomologicalComplex A c) := inferInstance

example : Injective D := endpointCofree_injective I

example : Mono embedding := endpointCofreeHom_mono K I a

example :
    (embedding.f 0 ≫ (endpointCofreeXIsoOfNoNext I 0 no_next_zero).hom).hom
      (ULift.up 1) ≠ 0 := by
  rw [endpointCofreeXIsoOfNoNext_hom, endpointCofreeHom_fst]
  exact cover_ne_zero (by decide : (1 : ZMod 6) ≠ 0)

example :
    ((embedding.f 1 ≫ endpointCofreeSecondProjection (c := c) I 1) ≫
      (endpointCofreeNextTermIso I rel_one_zero).hom).hom (ULift.up 1) =
        (Injective.ι N).hom (ULift.up (2 : ZMod 6)) ∧
    ((embedding.f 2 ≫ endpointCofreeSecondProjection (c := c) I 2) ≫
      (endpointCofreeNextTermIso I rel_two_one).hom).hom (ULift.up 1) =
        (Injective.ι N).hom (ULift.up (3 : ZMod 6)) :=
  ⟨embedding_second_one, embedding_second_two⟩

example :
    ((embedding.f 1 ≫ endpointCofreeSecondProjection (c := c) I 1) ≫
      (endpointCofreeNextTermIso I rel_one_zero).hom).hom (ULift.up 1) ≠ 0 ∧
    ((embedding.f 2 ≫ endpointCofreeSecondProjection (c := c) I 2) ≫
      (endpointCofreeNextTermIso I rel_two_one).hom).hom (ULift.up 1) ≠ 0 := by
  rw [embedding_second_one, embedding_second_two]
  exact ⟨cover_ne_zero (by decide : (2 : ZMod 6) ≠ 0),
    cover_ne_zero (by decide : (3 : ZMod 6) ≠ 0)⟩

private abbrev coefficientDouble : ∀ i : ℕ, I i ⟶ I i :=
  fun _ => (2 : ℤ) • 𝟙 J

example :
    ((embedding ≫ endpointCofreeMap (c := c) coefficientDouble).f 0 ≫
      endpointCofreeProjection (c := c) I 0).hom (ULift.up 1) =
        (Injective.ι N).hom (ULift.up (2 : ZMod 6)) ∧
    ((embedding ≫ endpointCofreeMap (c := c) coefficientDouble).f 0 ≫
      endpointCofreeProjection (c := c) I 0).hom (ULift.up 1) ≠ 0 := by
  have hvalue :
      ((embedding ≫ endpointCofreeMap (c := c) coefficientDouble).f 0 ≫
        endpointCofreeProjection (c := c) I 0).hom (ULift.up 1) =
          (Injective.ι N).hom (ULift.up (2 : ZMod 6)) := by
    rw [endpointCofreeHom_naturality K a coefficientDouble, endpointCofreeHom_fst]
    change (2 : ℤ) • (Injective.ι N).hom (ULift.up (1 : ZMod 6)) = _
    exact ((Injective.ι N).hom.toAddMonoidHom.map_zsmul (2 : ℤ)
      (ULift.up (1 : ZMod 6) : V)).symm.trans
        (congrArg (Injective.ι N).hom two_one)
  exact ⟨hvalue, by rw [hvalue]; exact cover_ne_zero (by decide : (2 : ZMod 6) ≠ 0)⟩

end NatBoundary

namespace Cyclic

private abbrev c := ComplexShape.down (ZMod 2)

private lemma rel_zero_one : c.Rel 0 1 := by decide
private lemma rel_one_zero : c.Rel 1 0 := by decide

private abbrev step (i : ZMod 2) : N ⟶ N :=
  if i = 0 then (2 : ℤ) • 𝟙 N else (3 : ℤ) • 𝟙 N

private lemma step_square {i j : ZMod 2} (hij : c.Rel i j) : step i ≫ step j = 0 := by
  fin_cases i <;> fin_cases j
  · exact False.elim ((by decide : ¬ c.Rel 0 0) hij)
  · change step (0 : ZMod 2) ≫ step (1 : ZMod 2) = 0
    simpa only [step, if_pos rfl, if_neg (by decide : (1 : ZMod 2) ≠ 0), ite_true]
      using two_three
  · change step (1 : ZMod 2) ≫ step (0 : ZMod 2) = 0
    simpa only [step, if_pos rfl, if_neg (by decide : (1 : ZMod 2) ≠ 0), ite_true]
      using three_two
  · exact False.elim ((by decide : ¬ c.Rel 1 1) hij)

private abbrev K : HomologicalComplex A c where
  X _ := N
  d i j := if c.Rel i j then step i else 0
  shape i j hij := by simp only [if_neg hij]
  d_comp_d' i j k hij hjk := by
    simp only [if_pos hij, if_pos hjk]
    exact step_square hij

private abbrev I : ZMod 2 → A := fun _ => J
private abbrev a : ∀ i : ZMod 2, K.X i ⟶ I i := fun _ => Injective.ι N
private abbrev D : HomologicalComplex A c := endpointCofree (c := c) I
private abbrev embedding : K ⟶ D := endpointCofreeHom K I a

private instance coefficient_injective : ∀ i, Injective (I i) :=
  fun _ => by change Injective J; infer_instance

private instance coefficient_mono : ∀ i, Mono (a i) :=
  fun _ => by change Mono (Injective.ι N); infer_instance

private lemma d_zero_one : (K.d 0 1).hom (ULift.up 1) = ULift.up (2 : ZMod 6) := by
  change (if c.Rel 0 1 then step 0 else 0).hom (ULift.up 1) = _
  rw [if_pos rel_zero_one]
  change (2 : ℤ) • (ULift.up (1 : ZMod 6) : V) = ULift.up (2 : ZMod 6)
  exact two_one

private lemma d_one_zero : (K.d 1 0).hom (ULift.up 1) = ULift.up (3 : ZMod 6) := by
  change (if c.Rel 1 0 then step 1 else 0).hom (ULift.up 1) = _
  rw [if_pos rel_one_zero]
  simp only [step, if_neg (by decide : (1 : ZMod 2) ≠ 0)]
  change (3 : ℤ) • (ULift.up (1 : ZMod 6) : V) = ULift.up (3 : ZMod 6)
  apply ULift.ext
  decide

private lemma embedding_second_zero :
    ((embedding.f 0 ≫ endpointCofreeSecondProjection (c := c) I 0) ≫
      (endpointCofreeNextTermIso I rel_zero_one).hom).hom (ULift.up 1) =
        (Injective.ι N).hom (ULift.up (2 : ZMod 6)) := by
  rw [endpointCofreeHom_snd_of_rel K I a rel_zero_one]
  change (Injective.ι N).hom ((K.d 0 1).hom (ULift.up 1)) = _
  rw [d_zero_one]

private lemma embedding_second_one :
    ((embedding.f 1 ≫ endpointCofreeSecondProjection (c := c) I 1) ≫
      (endpointCofreeNextTermIso I rel_one_zero).hom).hom (ULift.up 1) =
        (Injective.ι N).hom (ULift.up (3 : ZMod 6)) := by
  rw [endpointCofreeHom_snd_of_rel K I a rel_one_zero]
  change (Injective.ι N).hom ((K.d 1 0).hom (ULift.up 1)) = _
  rw [d_one_zero]

example : K.d 0 1 ≠ 0 ∧ K.d 1 0 ≠ 0 := by
  constructor
  · intro h
    have hx := d_zero_one
    rw [h] at hx
    exact (by decide : (0 : ZMod 6) ≠ 2) (congrArg ULift.down hx)
  · intro h
    have hx := d_one_zero
    rw [h] at hx
    exact (by decide : (0 : ZMod 6) ≠ 3) (congrArg ULift.down hx)

example : K.d 0 1 ≫ K.d 1 0 = 0 ∧ K.d 1 0 ≫ K.d 0 1 = 0 :=
  ⟨K.d_comp_d 0 1 0, K.d_comp_d 1 0 1⟩

example : EnoughInjectives (HomologicalComplex A c) := inferInstance

example : Injective D := endpointCofree_injective I

example : Mono embedding := endpointCofreeHom_mono K I a

example :
    ((embedding.f 0 ≫ endpointCofreeSecondProjection (c := c) I 0) ≫
      (endpointCofreeNextTermIso I rel_zero_one).hom).hom (ULift.up 1) ≠ 0 ∧
    ((embedding.f 1 ≫ endpointCofreeSecondProjection (c := c) I 1) ≫
      (endpointCofreeNextTermIso I rel_one_zero).hom).hom (ULift.up 1) ≠ 0 := by
  rw [embedding_second_zero, embedding_second_one]
  exact ⟨cover_ne_zero (by decide : (2 : ZMod 6) ≠ 0),
    cover_ne_zero (by decide : (3 : ZMod 6) ≠ 0)⟩

example :
    (endpointCofreeNextTermIso I rel_zero_one).inv ≫
      (biprod.inr : endpointCofreeNextTerm (c := c) I 0 ⟶ D.X 0) ≫
        D.d 0 1 ≫ endpointCofreeProjection (c := c) I 1 = 𝟙 J := by
  rw [endpointCofree_d I rel_zero_one]
  change (endpointCofreeNextTermIso I rel_zero_one).inv ≫
    (biprod.inr : endpointCofreeNextTerm (c := c) I 0 ⟶
      I 0 ⊞ endpointCofreeNextTerm (c := c) I 0) ≫
    ((biprod.snd : I 0 ⊞ endpointCofreeNextTerm (c := c) I 0 ⟶
      endpointCofreeNextTerm (c := c) I 0) ≫
      (endpointCofreeNextTermIso I rel_zero_one).hom ≫ biprod.inl) ≫
    (biprod.fst : I 1 ⊞ endpointCofreeNextTerm (c := c) I 1 ⟶ I 1) = 𝟙 J
  simp only [Category.assoc, biprod.inr_snd_assoc, biprod.inl_fst,
    Category.comp_id, Iso.inv_hom_id]

end Cyclic

end MathlibExtTest.EndpointCofree

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Data.ZMod.Basic
public import MathlibExt.Algebra.Homology.HomotopyLifting

/-!
# Null-homotopic lifts and extensions over the integers

The complexes have differential `(x, y) ↦ (y, 0)` in every integer degree.
Their contractions send `(x, y)` to `(0, x)`. The coefficient quotient
`ULift ℤ → ULift (ZMod 6)` gives a nonzero projective lift whose quotient
value is `2`. A native injective cover of `ULift (ZMod 6)` gives a nonzero
extension across a split coefficient inclusion.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HomotopyLiftingTests

open scoped Classical

private abbrev A := ModuleCat.{1} ℤ
private abbrev V := ULift.{1} ℤ
private abbrev W := ULift.{1} (ZMod 6)
private abbrev P : A := ModuleCat.of ℤ V
private abbrev N : A := ModuleCat.of ℤ W
private abbrev J : A := Injective.under N

private abbrev splitComplex (M : A) : ChainComplex A ℤ where
  X _ := M ⊞ M
  d i j := if (ComplexShape.down ℤ).Rel i j then biprod.snd ≫ biprod.inl else 0
  shape i j hij := by simp only [if_neg hij]
  d_comp_d' i j k hij hjk := by
    simp only [if_pos hij, if_pos hjk, Category.assoc, biprod.inl_snd_assoc,
      comp_zero, zero_comp]

private def splitHom {M M' : A} (f : M ⟶ M') : splitComplex M ⟶ splitComplex M' where
  f _ := biprod.map f f
  comm' i j hij := by
    change biprod.map f f ≫
        (if (ComplexShape.down ℤ).Rel i j then biprod.snd ≫ biprod.inl else 0) =
      (if (ComplexShape.down ℤ).Rel i j then biprod.snd ≫ biprod.inl else 0) ≫
        biprod.map f f
    simp only [ite_eq_left hij, Category.assoc, biprod.map_snd_assoc, biprod.inl_map]

private lemma splitHom_f {M M' : A} (f : M ⟶ M') (n : ℤ) :
    (splitHom f).f n = biprod.map f f := rfl

private lemma splitBoundary_eq (M : A) :
    Homotopy.nullHomotopicMap' (C := splitComplex M) (D := splitComplex M)
      (fun i j (_ : (ComplexShape.down ℤ).Rel j i) =>
        (biprod.fst : (splitComplex M).X i ⟶ M) ≫ biprod.inr) = 𝟙 (splitComplex M) := by
  apply HomologicalComplex.hom_ext
  intro n
  have r₂₁ : (ComplexShape.down ℤ).Rel (n + 1) n := by
    simp only [ComplexShape.down_Rel]
  have r₁₀ : (ComplexShape.down ℤ).Rel n (n - 1) := by
    simp only [ComplexShape.down_Rel, sub_add_cancel]
  rw [Homotopy.nullHomotopicMap'_f r₂₁ r₁₀]
  change
    (if (ComplexShape.down ℤ).Rel n (n - 1) then biprod.snd ≫ biprod.inl else 0) ≫
        (biprod.fst ≫ biprod.inr) +
      (biprod.fst ≫ biprod.inr) ≫
        (if (ComplexShape.down ℤ).Rel (n + 1) n then biprod.snd ≫ biprod.inl else 0) =
      𝟙 (M ⊞ M)
  simp only [if_pos r₁₀, if_pos r₂₁, Category.assoc, biprod.inl_fst_assoc,
    biprod.inr_snd_assoc, Category.id_comp]
  rw [add_comm]
  exact biprod.total

private def splitContraction (M : A) : Homotopy (𝟙 (splitComplex M)) 0 :=
  (Homotopy.ofEq (splitBoundary_eq M).symm).trans
    (Homotopy.nullHomotopy' (C := splitComplex M) (D := splitComplex M)
      (fun i j (_ : (ComplexShape.down ℤ).Rel j i) =>
      (biprod.fst : (splitComplex M).X i ⟶ M) ≫ biprod.inr))

private def splitNullHomotopy {M : A} {K : ChainComplex A ℤ}
    (f : splitComplex M ⟶ K) : Homotopy f 0 :=
  (Homotopy.ofEq (by simp)).trans
    (((splitContraction M).compRight f).trans (Homotopy.ofEq (by simp)))

private instance coefficient_projective : Projective P :=
  ModuleCat.projective_of_free (Module.Free.chooseBasis ℤ V)

private instance complex_terms_projective : ∀ n, Projective ((splitComplex P).X n) :=
  fun _ => by change Projective (P ⊞ P); infer_instance

private instance complex_terms_injective : ∀ n, Injective ((splitComplex J).X n) :=
  fun _ => by change Injective (J ⊞ J); infer_instance

private abbrev coefficientQuotient : P ⟶ N :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton ℤ W (ULift.up 1)).comp
    (ULift.moduleEquiv : V ≃ₗ[ℤ] ℤ).toLinearMap)

private lemma coefficientQuotient_apply (n : ℤ) :
    (coefficientQuotient.hom (ULift.up n)).down = (n : ZMod 6) := by
  change n • (1 : ZMod 6) = (n : ZMod 6)
  simp only [zsmul_eq_mul, mul_one]

private instance coefficientQuotient_epi : Epi coefficientQuotient := by
  apply (ModuleCat.epi_iff_surjective coefficientQuotient).mpr
  intro x
  refine ⟨ULift.up (x.down.val : ℤ), ?_⟩
  apply ULift.ext
  rw [coefficientQuotient_apply]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

private abbrev quotientMap := splitHom coefficientQuotient
private abbrev doubleQuotientMap := splitHom (2 • coefficientQuotient)

private instance quotientMap_epi : Epi quotientMap := by
  apply HomologicalComplex.epi_of_epi_f
  intro n
  change Epi (biprod.map coefficientQuotient coefficientQuotient)
  infer_instance

private abbrev liftedMap : splitComplex P ⟶ splitComplex P :=
  (splitNullHomotopy doubleQuotientMap).projectiveLift quotientMap

private lemma liftedMap_comp : liftedMap ≫ quotientMap = doubleQuotientMap :=
  (splitNullHomotopy doubleQuotientMap).projectiveLift_comp quotientMap

private lemma liftedMap_coordinate (n : ℤ) :
    (biprod.inr : P ⟶ P ⊞ P) ≫ liftedMap.f n ≫ quotientMap.f n ≫
      (biprod.snd : N ⊞ N ⟶ N) = 2 • coefficientQuotient := by
  have h := HomologicalComplex.congr_hom liftedMap_comp n
  change liftedMap.f n ≫ quotientMap.f n = doubleQuotientMap.f n at h
  rw [← Category.assoc (liftedMap.f n) (quotientMap.f n) biprod.snd, h]
  simp only [splitHom_f, Category.assoc, biprod.inr_map_assoc, biprod.inr_snd,
    Category.comp_id]

example : (biprod.inr : N ⟶ N ⊞ N) ≫ (splitComplex N).d (-2) (-3) = biprod.inl := by
  change biprod.inr ≫
    (if (ComplexShape.down ℤ).Rel (-2) (-3) then biprod.snd ≫ biprod.inl else 0) = _
  simp [ComplexShape.down_Rel, Category.assoc]

example : (splitComplex N).d (-2) (-3) ≫ (splitComplex N).d (-3) (-4) = 0 :=
  (splitComplex N).d_comp_d (-2) (-3) (-4)

example : (biprod.inl : N ⟶ N ⊞ N) ≫ (splitContraction N).hom (-3) (-2) =
    biprod.inr := by
  dsimp only [splitContraction, Homotopy.trans, Homotopy.ofEq,
    Homotopy.nullHomotopy', Homotopy.nullHomotopy]
  simp [ComplexShape.down_Rel, Category.assoc]

example : Projective (splitComplex P) :=
  HomologicalComplex.projective_of_id_homotopic_zero (splitContraction P)

example : (((biprod.inr : P ⟶ P ⊞ P) ≫ liftedMap.f (-2) ≫ quotientMap.f (-2) ≫
    (biprod.snd : N ⊞ N ⟶ N)).hom (ULift.up 1)).down = (2 : ZMod 6) := by
  rw [liftedMap_coordinate]
  change (2 : ℤ) • (coefficientQuotient.hom (ULift.up 1)).down = (2 : ZMod 6)
  rw [coefficientQuotient_apply]
  decide

example : liftedMap ≠ 0 := by
  intro hzero
  have h := liftedMap_coordinate (-2)
  rw [hzero] at h
  simp only [HomologicalComplex.zero_f_apply, zero_comp, comp_zero] at h
  have hx := congrArg (fun f : P ⟶ N => (f.hom (ULift.up 1)).down) h
  change 0 = (2 : ℤ) • (coefficientQuotient.hom (ULift.up 1)).down at hx
  rw [coefficientQuotient_apply] at hx
  exact (by decide : (0 : ZMod 6) ≠ (2 : ℤ) • (1 : ZMod 6)) hx

example : Nonempty (Homotopy liftedMap 0) :=
  ⟨(splitNullHomotopy doubleQuotientMap).projectiveLiftNullHomotopy quotientMap⟩

private abbrev coefficientInclusion : N ⟶ N ⊞ N := biprod.inl
private abbrev inclusionMap := splitHom coefficientInclusion
private abbrev coverMap := splitHom (Injective.ι N)

private instance inclusionMap_mono : Mono inclusionMap := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  change Mono (biprod.map coefficientInclusion coefficientInclusion)
  infer_instance

private abbrev extendedMap : splitComplex (N ⊞ N) ⟶ splitComplex J :=
  (splitNullHomotopy coverMap).injectiveExtension inclusionMap

private lemma inclusionMap_comp : inclusionMap ≫ extendedMap = coverMap :=
  (splitNullHomotopy coverMap).comp_injectiveExtension inclusionMap

private lemma cover_one_ne_zero : (Injective.ι N).hom (ULift.up 1) ≠ 0 := by
  intro hzero
  have hi := (ModuleCat.mono_iff_injective (Injective.ι N)).mp inferInstance
  have h := hi (hzero.trans ((Injective.ι N).hom.map_zero).symm)
  have h' := congrArg ULift.down h
  change (1 : ZMod 6) = 0 at h'
  exact (by decide : (1 : ZMod 6) ≠ 0) h'

private lemma extendedMap_coordinate (n : ℤ) :
    (biprod.inr : N ⟶ N ⊞ N) ≫ inclusionMap.f n ≫ extendedMap.f n ≫
      (biprod.snd : J ⊞ J ⟶ J) = Injective.ι N := by
  have h := HomologicalComplex.congr_hom inclusionMap_comp n
  change inclusionMap.f n ≫ extendedMap.f n = coverMap.f n at h
  rw [← Category.assoc (inclusionMap.f n) (extendedMap.f n) biprod.snd, h]
  simp only [splitHom_f, Category.assoc, biprod.inr_map_assoc, biprod.inr_snd,
    Category.comp_id]

example : Injective (splitComplex J) :=
  HomologicalComplex.injective_of_id_homotopic_zero (splitContraction J)

example : ((biprod.inr : N ⟶ N ⊞ N) ≫ inclusionMap.f (-2) ≫ extendedMap.f (-2) ≫
    (biprod.snd : J ⊞ J ⟶ J)).hom (ULift.up 1) ≠ 0 := by
  rw [extendedMap_coordinate]
  exact cover_one_ne_zero

example : extendedMap ≠ 0 := by
  intro hzero
  have h := extendedMap_coordinate (-2)
  rw [hzero] at h
  simp only [HomologicalComplex.zero_f_apply, zero_comp, comp_zero] at h
  have hx := congrArg (fun f : N ⟶ J => f.hom (ULift.up 1)) h
  exact cover_one_ne_zero hx.symm

example : Nonempty (Homotopy extendedMap 0) :=
  ⟨(splitNullHomotopy coverMap).injectiveExtensionNullHomotopy inclusionMap⟩

end HomotopyLiftingTests

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.ExactCategory.Basic
public import MathlibExt.CategoryTheory.ExactCategory.MorphismProperty
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Biproducts of admissible exact short complexes

In an exact category, the componentwise binary biproduct (direct sum) of two
admissible exact short complexes is admissible exact.

The biproduct map on admissible monos is an admissible mono: it factors as two
successive pushouts of the component admissible monos along the biproduct
inclusions, and admissible monos compose. The full biproduct sequence is then
admissible by transporting the witness sequence for that mono along the
canonical cokernel comparison isomorphism.

## Main definitions and results

* `CategoryTheory.ExactCategory.biprodShortComplex`: componentwise biproduct
  of two short complexes, via `biprod.map`.
* `CategoryTheory.ExactCategory.isAdmissibleExact_biprod`: the biproduct of
  two admissible exact short complexes is admissible exact.

Nonclaims: no `ExactCategory (C × C)`, no `biprodFunctor.IsExact`, no
Waldhausen additivity, K/G-theory, realization, spectra, or Q/S comparison.
-/

@[expose] public section

open CategoryTheory Limits Preadditive ZeroObject

universe v u

namespace CategoryTheory

namespace ExactCategory

section BiprodLower

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

/-- The componentwise biproduct maps compose to zero. -/
lemma biprodShortComplex_zero (S T : ShortComplex C) :
    biprod.map S.f T.f ≫ biprod.map S.g T.g = 0 := by
  apply biprod.hom_ext
  · rw [zero_comp, Category.assoc, biprod.map_fst, ← Category.assoc,
      biprod.map_fst, Category.assoc, S.zero, comp_zero]
  · rw [zero_comp, Category.assoc, biprod.map_snd, ← Category.assoc,
      biprod.map_snd, Category.assoc, T.zero, comp_zero]

/-- Componentwise binary biproduct of two short complexes, via `biprod.map`. -/
noncomputable def biprodShortComplex (S T : ShortComplex C) : ShortComplex C :=
  ShortComplex.mk (biprod.map S.f T.f) (biprod.map S.g T.g)
    (biprodShortComplex_zero S T)

/-- The `f` field of `biprodShortComplex` is the biproduct map. -/
@[simp]
theorem biprodShortComplex_f (S T : ShortComplex C) :
    (biprodShortComplex S T).f = biprod.map S.f T.f :=
  rfl

/-- The `g` field of `biprodShortComplex` is the biproduct map. -/
@[simp]
theorem biprodShortComplex_g (S T : ShortComplex C) :
    (biprodShortComplex S T).g = biprod.map S.g T.g :=
  rfl

end BiprodLower

section BiprodExact

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- First pushout square: `S.f` pushed along the left inclusion. -/
private noncomputable def pushoutStep1_isColimit (S T : ShortComplex C) :
    IsColimit (PushoutCocone.mk (biprod.map S.f (𝟙 T.X₁))
      (biprod.inl : S.X₂ ⟶ S.X₂ ⊞ T.X₁) (biprod.inl_map S.f (𝟙 T.X₁))) := by
  refine PushoutCocone.IsColimit.mk _
    (fun s => biprod.desc s.inr (biprod.inr ≫ s.inl)) ?_ ?_ ?_
  · intro s
    apply biprod.hom_ext'
    · rw [← Category.assoc, biprod.inl_map, Category.assoc, biprod.inl_desc]
      exact s.condition.symm
    · rw [← Category.assoc, biprod.inr_map, Category.id_comp, biprod.inr_desc]
  · intro s
    exact biprod.inl_desc _ _
  · intro s m' h1 h2
    apply biprod.hom_ext'
    · rw [h2, biprod.inl_desc]
    · have hr : (biprod.inr : T.X₁ ⟶ S.X₂ ⊞ T.X₁) =
          (biprod.inr : T.X₁ ⟶ S.X₁ ⊞ T.X₁) ≫ biprod.map S.f (𝟙 T.X₁) := by
        rw [biprod.inr_map, Category.id_comp]
      have hL : (biprod.inr : T.X₁ ⟶ S.X₂ ⊞ T.X₁) ≫ m' =
          (biprod.inr : T.X₁ ⟶ S.X₁ ⊞ T.X₁) ≫ s.inl := by
        rw [hr, Category.assoc, h1]
      rw [biprod.inr_desc]
      exact hL

/-- Second pushout square: `T.f` pushed along the right inclusion. -/
private noncomputable def pushoutStep2_isColimit (S T : ShortComplex C) :
    IsColimit (PushoutCocone.mk (biprod.map (𝟙 S.X₂) T.f)
      (biprod.inr : T.X₂ ⟶ S.X₂ ⊞ T.X₂) (biprod.inr_map (𝟙 S.X₂) T.f)) := by
  refine PushoutCocone.IsColimit.mk _
    (fun s => biprod.desc (biprod.inl ≫ s.inl) s.inr) ?_ ?_ ?_
  · intro s
    apply biprod.hom_ext'
    · rw [← Category.assoc, biprod.inl_map, Category.id_comp, biprod.inl_desc]
    · rw [← Category.assoc, biprod.inr_map, Category.assoc, biprod.inr_desc]
      exact s.condition.symm
  · intro s
    exact biprod.inr_desc _ _
  · intro s m' h1 h2
    apply biprod.hom_ext'
    · have hl : (biprod.inl : S.X₂ ⟶ S.X₂ ⊞ T.X₂) =
          (biprod.inl : S.X₂ ⟶ S.X₂ ⊞ T.X₁) ≫ biprod.map (𝟙 S.X₂) T.f := by
        rw [biprod.inl_map, Category.id_comp]
      have hL : (biprod.inl : S.X₂ ⟶ S.X₂ ⊞ T.X₂) ≫ m' =
          (biprod.inl : S.X₂ ⟶ S.X₂ ⊞ T.X₁) ≫ s.inl := by
        rw [hl, Category.assoc, h1]
      rw [biprod.inl_desc]
      exact hL
    · rw [h2, biprod.inr_desc]

/-- The biproduct cokernel comparison: `biprod.map S.g T.g` is a cokernel of
the biproduct mono, from the component cokernel witnesses. -/
private noncomputable def biprod_cokernel_isColimit (S T : ShortComplex C)
    (hS : IsAdmissibleExact S) (hT : IsAdmissibleExact T) :
    IsColimit (CokernelCofork.ofπ (biprod.map S.g T.g)
      (biprodShortComplex_zero S T)) := by
  have hC_S := isColimit_cokernelCofork_of_isAdmissibleExact hS
  have hC_T := isColimit_cokernelCofork_of_isAdmissibleExact hT
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun {W} g' eq' =>
      biprod.desc
        (hC_S.desc (CokernelCofork.ofπ (biprod.inl ≫ g') (by
          have key := (biprod.inl_map S.f T.f).symm
          rw [← Category.assoc, key, Category.assoc, eq', comp_zero])))
        (hC_T.desc (CokernelCofork.ofπ (biprod.inr ≫ g') (by
          have key := (biprod.inr_map S.f T.f).symm
          rw [← Category.assoc, key, Category.assoc, eq', comp_zero])))) ?_ ?_
  · intro W g' eq'
    apply biprod.hom_ext'
    · rw [← Category.assoc, biprod.inl_map, Category.assoc, biprod.inl_desc]
      exact Cofork.IsColimit.π_desc hC_S
    · rw [← Category.assoc, biprod.inr_map, Category.assoc, biprod.inr_desc]
      exact Cofork.IsColimit.π_desc hC_T
  · intro W g' eq' m hm
    apply biprod.hom_ext'
    · have e1 : (biprod.inl : S.X₃ ⟶ S.X₃ ⊞ T.X₃) ≫ m =
          hC_S.desc (CokernelCofork.ofπ (biprod.inl ≫ g') (by
            have key := (biprod.inl_map S.f T.f).symm
            rw [← Category.assoc, key, Category.assoc, eq', comp_zero])) := by
        apply Cofork.IsColimit.hom_ext hC_S
        change S.g ≫ ((biprod.inl : S.X₃ ⟶ S.X₃ ⊞ T.X₃) ≫ m) =
          S.g ≫ hC_S.desc (CokernelCofork.ofπ (biprod.inl ≫ g') _)
        have keyS := (biprod.inl_map S.g T.g).symm
        rw [← Category.assoc, keyS, Category.assoc, hm]
        exact (Cofork.IsColimit.π_desc
          (t := CokernelCofork.ofπ (biprod.inl ≫ g') _) hC_S).symm
      rw [biprod.inl_desc]
      exact e1
    · have e2 : (biprod.inr : T.X₃ ⟶ S.X₃ ⊞ T.X₃) ≫ m =
          hC_T.desc (CokernelCofork.ofπ (biprod.inr ≫ g') (by
            have key := (biprod.inr_map S.f T.f).symm
            rw [← Category.assoc, key, Category.assoc, eq', comp_zero])) := by
        apply Cofork.IsColimit.hom_ext hC_T
        change T.g ≫ ((biprod.inr : T.X₃ ⟶ S.X₃ ⊞ T.X₃) ≫ m) =
          T.g ≫ hC_T.desc (CokernelCofork.ofπ (biprod.inr ≫ g') _)
        have keyT := (biprod.inr_map S.g T.g).symm
        rw [← Category.assoc, keyT, Category.assoc, hm]
        exact (Cofork.IsColimit.π_desc
          (t := CokernelCofork.ofπ (biprod.inr ≫ g') _) hC_T).symm
      rw [biprod.inr_desc]
      exact e2

/-- The componentwise binary biproduct of two admissible exact short complexes
is admissible exact. -/
theorem isAdmissibleExact_biprod {S T : ShortComplex C}
    (hS : IsAdmissibleExact S) (hT : IsAdmissibleExact T) :
    IsAdmissibleExact (biprodShortComplex S T) := by
  have hfS : IsAdmissibleMono S.f := isAdmissibleMono_f hS
  have hfT : IsAdmissibleMono T.f := isAdmissibleMono_f hT
  have hm1 : IsAdmissibleMono (biprod.map S.f (𝟙 T.X₁)) :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout
      (P := admissibleMonosOf C IsAdmissibleExact)
      (IsPushout.of_isColimit (pushoutStep1_isColimit S T)) hfS
  have hm2 : IsAdmissibleMono (biprod.map (𝟙 S.X₂) T.f) :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout
      (P := admissibleMonosOf C IsAdmissibleExact)
      (IsPushout.of_isColimit (pushoutStep2_isColimit S T)) hfT
  have hf : IsAdmissibleMono (biprod.map S.f T.f) := by
    have hcomp : biprod.map S.f T.f =
        biprod.map S.f (𝟙 T.X₁) ≫ biprod.map (𝟙 S.X₂) T.f := by
      apply biprod.hom_ext
      · rw [Category.assoc, biprod.map_fst, biprod.map_fst, Category.comp_id,
          biprod.map_fst]
      · rw [Category.assoc, biprod.map_snd, biprod.map_snd, ← Category.assoc,
          biprod.map_snd, Category.comp_id]
    rw [hcomp]
    exact admissibleMono_comp.comp_mem _ _ hm1 hm2
  have hC_B := biprod_cokernel_isColimit S T hS hT
  exact isAdmissibleExact_of_isAdmissibleMono_isColimit hf hC_B

end BiprodExact

end ExactCategory

end CategoryTheory

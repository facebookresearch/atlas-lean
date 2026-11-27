/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Abelian.Projective.PresentationComplex
public import MathlibExt.CategoryTheory.Abelian.Projective.PresentationSplitRow
public import MathlibExt.CategoryTheory.Abelian.Projective.Horseshoe
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Projective horseshoe of a short exact presentation

Let `A → B → X` be short exact in an abelian category, with `A,B`
projective. Resolve `A` by its degree-zero single resolution and `X`
by the two-term presentation `A → B`. The middle resolution of `B`
is `A → A ⊞ B` with differential `[-id,f]` and augmentation `[f,id]`.
Left inclusion and right projection give a degreewise split horseshoe,
whose right map in degree one is the identity of `A`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ProjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (S : ShortComplex C) (hS : S.ShortExact) [Projective S.X₁] [Projective S.X₂]

/-- In an abelian category `C`, let `S` be a short complex with
projective left object `A`. The single chain complex concentrated
in degree zero at `A`, augmented by its identity, resolves `A`. -/
abbrev presentationLeftResolution : ProjectiveResolution S.X₁ := ProjectiveResolution.self S.X₁

/-- In an abelian category `C`, let `S : A → B → X` be a short
complex with `A,B` projective. The two-term complex
`A → A ⊞ B`, with differential `[-id,S.f]` and augmentation
`[S.f,id]`, is a projective resolution of `B`. -/
abbrev presentationMiddleResolution : ProjectiveResolution S.X₂ :=
  @ofPresentation C _ _ (presentationMiddleRow S) (presentationMiddleRow_shortExact S)
    (show Projective S.X₁ from inferInstance)
    (show Projective (S.X₁ ⊞ S.X₂) from inferInstance)

/-- In an abelian category `C`, let `S : A → B → X` be a short
complex with `A,B` projective. The left inclusion gives a chain map
from the single resolution of `A` to the split middle resolution
`A → A ⊞ B`. -/
def presentationHorseshoeInclusion :
    (presentationLeftResolution S).complex ⟶ (presentationMiddleResolution S).complex :=
  (ChainComplex.fromSingle₀Equiv (presentationMiddleResolution S).complex S.X₁).symm biprod.inl

/-- Let `C` be abelian and `S : A → B → X` short exact, with
`A,B` projective. The chain map from the split middle resolution to the
presentation resolution of `X` is the second projection
`A ⊞ B → B` in degree zero and the identity on `A` in degree one. -/
def presentationHorseshoeProjection :
    (presentationMiddleResolution S).complex ⟶ (ofPresentation S hS).complex :=
  ChainComplex.ofHom
    (fun n => match n with
      | 0 => biprod.snd
      | 1 => 𝟙 S.X₁
      | _ + 2 => 0)
    (by
      intro n
      cases n with
      | zero =>
          have hR : (ofPresentation S hS).complex.d 1 0 = S.f := presentationComplex_d_zero S
          have hM : (presentationMiddleResolution S).complex.d 1 0 =
              (biprod.lift (-𝟙 S.X₁) S.f) := presentationComplex_d_zero (presentationMiddleRow S)
          dsimp only
          exact (congrArg (fun q => (𝟙 S.X₁) ≫ q) hR).trans
            ((Category.id_comp S.f).trans
              ((biprod.lift_snd (-𝟙 S.X₁) S.f).symm.trans
                (congrArg (fun q => q ≫ (biprod.snd : S.X₁ ⊞ S.X₂ ⟶ S.X₂)) hM.symm)))
      | succ n =>
          have hR : (ofPresentation S hS).complex.d (n + 2) (n + 1) = 0 :=
            presentationComplex_d_succ S n
          have hM : (presentationMiddleResolution S).complex.d (n + 2) (n + 1) = 0 :=
            presentationComplex_d_succ (presentationMiddleRow S) n
          dsimp only
          rw [zero_comp]
          symm
          exact (congrArg
            (fun q : (presentationMiddleResolution S).complex.X (n + 2) ⟶
                (presentationMiddleResolution S).complex.X (n + 1) =>
              q ≫ (show (presentationMiddleResolution S).complex.X (n + 1) ⟶
                  (ofPresentation S hS).complex.X (n + 1) from
                match n + 1 with
                | 0 => biprod.snd
                | 1 => 𝟙 S.X₁
                | _ + 2 => 0)) hM).trans zero_comp)

/-- In an abelian category `C`, let `S : A → B → X` be a short
complex with `A,B` projective. In degree zero, the inclusion from
the single resolution of `A` is `A → A ⊞ B`, the left biproduct
inclusion. -/
theorem presentationHorseshoeInclusion_f_zero :
    (presentationHorseshoeInclusion S).f 0 =
      (biprod.inl : S.X₁ ⟶ S.X₁ ⊞ S.X₂) :=
  ChainComplex.fromSingle₀Equiv_symm_apply_f_zero _

/-- In an abelian category `C`, let `S : A → B → X` be a short
complex with `A,B` projective. The inclusion from the single
resolution of `A` is zero in every positive degree because its
source term is zero. -/
theorem presentationHorseshoeInclusion_f_succ (n : ℕ) :
    (presentationHorseshoeInclusion S).f (n + 1) = 0 :=
  ChainComplex.fromSingle₀Equiv_symm_apply_f_succ _ n

/-- Let `C` be abelian and `S : A → B → X` short exact, with
`A,B` projective. The degree-zero projection from the split middle resolution
to the quotient presentation is the right biproduct projection
`A ⊞ B → B`. -/
theorem presentationHorseshoeProjection_f_zero :
    (presentationHorseshoeProjection S hS).f 0 =
      (biprod.snd : S.X₁ ⊞ S.X₂ ⟶ S.X₂) := rfl

/-- Let `C` be abelian and `S : A → B → X` short exact, with
`A,B` projective. The degree-one projection from the split middle resolution
to the quotient presentation is `𝟙 A`. -/
theorem presentationHorseshoeProjection_f_one :
    (presentationHorseshoeProjection S hS).f 1 = 𝟙 S.X₁ := rfl

/-- Let `C` be abelian and `S : A → B → X` short exact, with
`A,B` projective. The chain inclusion from the single resolution of `A`,
followed by the projection to the presentation resolution of `X`,
has zero composite. -/
theorem presentationHorseshoe_zero :
    presentationHorseshoeInclusion S ≫ presentationHorseshoeProjection S hS = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
      rw [HomologicalComplex.comp_f, presentationHorseshoeInclusion_f_zero,
        presentationHorseshoeProjection_f_zero]
      exact biprod.inl_snd
  | succ n =>
      rw [HomologicalComplex.comp_f, presentationHorseshoeInclusion_f_succ, zero_comp]
      rfl

/-- Let `C` be abelian and `S : A → B → X` short exact, with
`A,B` projective. The single resolution of `A`, split middle resolution of `B`,
and presentation resolution of `X`, with their inclusion and
projection, form a short complex of nonnegative chain complexes. -/
def presentationHorseshoeDiagram : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk (presentationHorseshoeInclusion S) (presentationHorseshoeProjection S hS)
    (presentationHorseshoe_zero S hS)

/-- Let `C` be abelian and `S : A → B → X` short exact, with
`A,B` projective. The row of presentation-horseshoe resolution terms has a
chosen splitting in every degree `n`: the biproduct row in degree
zero, the row with identity on `A` in degree one, and zero rows thereafter. -/
def presentationHorseshoeSplitting (n : ℕ) :
    (ShortComplex.mk ((presentationHorseshoeInclusion S).f n)
      ((presentationHorseshoeProjection S hS).f n)
      (HomologicalComplex.congr_hom (presentationHorseshoe_zero S hS) n)).Splitting := by
  cases n with
  | zero =>
      simp only [presentationHorseshoeInclusion_f_zero, presentationHorseshoeProjection_f_zero]
      exact ShortComplex.Splitting.ofHasBinaryBiproduct S.X₁ S.X₂
  | succ n =>
      cases n with
      | zero =>
          apply ShortComplex.Splitting.ofIsZeroOfIsIso
          · exact HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 S.X₁ 1 (by simp)
          · exact Eq.mpr (congrArg IsIso (presentationHorseshoeProjection_f_one S hS))
              (show IsIso (𝟙 S.X₁) from inferInstance)
      | succ n =>
          apply ShortComplex.Splitting.ofIsZero
          · exact HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 S.X₁
              (n + 2) (by omega)
          · change IsZero (0 : C)
            exact isZero_zero C
          · change IsZero (0 : C)
            exact isZero_zero C

/-- Let `C` be abelian and `S : A → B → X` short exact, with
`A,B` projective. The split middle resolution, inclusion and projection give
horseshoe data for `S` with the single resolution of `A` on the left
and the presentation resolution of `X` on the right. -/
def presentationHorseshoe : HorseshoeData hS (presentationLeftResolution S)
    (ofPresentation S hS) where
  middle := presentationMiddleResolution S
  i := presentationHorseshoeInclusion S
  p := presentationHorseshoeProjection S hS
  zero := presentationHorseshoe_zero S hS
  shortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    exact fun n => (presentationHorseshoeSplitting S hS n).shortExact
  i_augmentation := by
    apply (ChainComplex.toSingle₀Equiv _ _).injective
    apply Subtype.ext
    change (presentationHorseshoeInclusion S ≫ (presentationMiddleResolution S).π).f 0 =
      ((presentationLeftResolution S).π ≫ (ChainComplex.single₀ C).map S.f).f 0
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      presentationHorseshoeInclusion_f_zero, ChainComplex.single₀_map_f_zero]
    have hm : (presentationMiddleResolution S).π.f 0 = biprod.desc S.f (𝟙 S.X₂) :=
      presentationAugmentation_f_zero (presentationMiddleRow S)
    have hl : (presentationLeftResolution S).π.f 0 = 𝟙 S.X₁ := rfl
    exact (congrArg (fun q => (biprod.inl : S.X₁ ⟶ S.X₁ ⊞ S.X₂) ≫ q) hm).trans
      ((biprod.inl_desc S.f (𝟙 S.X₂)).trans
        ((Category.id_comp S.f).symm.trans (congrArg (fun q => q ≫ S.f) hl.symm)))
  p_augmentation := by
    apply (ChainComplex.toSingle₀Equiv _ _).injective
    apply Subtype.ext
    change (presentationHorseshoeProjection S hS ≫ (ofPresentation S hS).π).f 0 =
      ((presentationMiddleResolution S).π ≫ (ChainComplex.single₀ C).map S.g).f 0
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      presentationHorseshoeProjection_f_zero, ChainComplex.single₀_map_f_zero]
    have hm : (presentationMiddleResolution S).π.f 0 = biprod.desc S.f (𝟙 S.X₂) :=
      presentationAugmentation_f_zero (presentationMiddleRow S)
    have hr : (ofPresentation S hS).π.f 0 = S.g := presentationAugmentation_f_zero S
    have h : (biprod.snd : S.X₁ ⊞ S.X₂ ⟶ S.X₂) ≫ S.g =
        biprod.desc S.f (𝟙 S.X₂) ≫ S.g := by
      apply biprod.hom_ext'
      · rw [← Category.assoc, biprod.inl_snd, zero_comp,
          ← Category.assoc, biprod.inl_desc, S.zero]
      · rw [← Category.assoc, biprod.inr_snd, Category.id_comp,
          ← Category.assoc, biprod.inr_desc, Category.id_comp]
    exact (congrArg (fun q => (biprod.snd : S.X₁ ⊞ S.X₂ ⟶ S.X₂) ≫ q) hr).trans
      (h.trans (congrArg (fun q => q ≫ S.g) hm.symm))

end CategoryTheory.ProjectiveResolution

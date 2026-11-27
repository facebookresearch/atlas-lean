/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.ExactCategory.Bicartesian
public import MathlibExt.CategoryTheory.ExactCategory.AdmissibleEpiKernelComposition

/-!
# The middle-row direction of the admissible three-by-three lemma

For `D : ShortComplex (ShortComplex C)` in a chosen exact structure on `C`,
the top and bottom admissible exact rows, together with the admissible exact
columns, determine admissible exactness of the middle row `D.X₂`, whose
composite is already zero. A pushout factors its last map as a composite of
admissible epimorphisms. The kernel-composition sequence identifies its
given first object with the kernel of that composite.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.ExactCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- Let `C` be an additive category with an exact structure, and let
`D : ShortComplex (ShortComplex C)` be a short complex of short complexes.
Its rows are `D.X₁`, `D.X₂`, and `D.X₃`; its columns are the short complexes
`D.map ShortComplex.π₁`, `D.map ShortComplex.π₂`, and
`D.map ShortComplex.π₃`. All row and column composites are therefore zero,
and the squares commute. If the three columns and the top and bottom rows
are admissible exact, then the middle row `D.X₂` is admissible exact.
In particular, the middle row is already a short complex, not just a pair
of maps in a commuting grid. -/
theorem isAdmissibleExact_middle_of_three_by_three
    (D : ShortComplex (ShortComplex C))
    (hA : IsAdmissibleExact D.X₁) (hZ : IsAdmissibleExact D.X₃)
    (h₁ : IsAdmissibleExact (D.map (ShortComplex.π₁ : ShortComplex C ⥤ C)))
    (h₂ : IsAdmissibleExact (D.map (ShortComplex.π₂ : ShortComplex C ⥤ C)))
    (h₃ : IsAdmissibleExact (D.map (ShortComplex.π₃ : ShortComplex C ⥤ C))) :
    IsAdmissibleExact D.X₂ := by
  let A : ShortComplex C := D.X₁
  let B : ShortComplex C := D.X₂
  let Z : ShortComplex C := D.X₃
  let α : A ⟶ B := D.f
  let β : B ⟶ Z := D.g
  let w₁ : α.τ₁ ≫ β.τ₁ = 0 :=
    (D.map (ShortComplex.π₁ : ShortComplex C ⥤ C)).zero
  let w₂ : α.τ₂ ≫ β.τ₂ = 0 :=
    (D.map (ShortComplex.π₂ : ShortComplex C ⥤ C)).zero
  let w₃ : α.τ₃ ≫ β.τ₃ = 0 :=
    (D.map (ShortComplex.π₃ : ShortComplex C ⥤ C)).zero
  let C₁ : ShortComplex C := ShortComplex.mk α.τ₁ β.τ₁ w₁
  let C₃ : ShortComplex C := ShortComplex.mk α.τ₃ β.τ₃ w₃
  have hC₁ : IsAdmissibleExact C₁ := h₁
  have hC₃ : IsAdmissibleExact C₃ := h₃
  obtain ⟨P, j, k, hpo, _hj⟩ :=
    admissibleMono_pushout A.X₂ B.X₂ α.τ₂ (isAdmissibleMono_f h₂)
      A.X₃ A.g
  let q : P ⟶ Z.X₂ :=
    pushoutQuotientMap A.g α.τ₂ β.τ₂ j k w₂ hpo
  have hjq : j ≫ q = 0 :=
    pushoutQuotientMap_x A.g α.τ₂ β.τ₂ j k w₂ hpo
  have hkq : k ≫ q = β.τ₂ :=
    pushoutQuotientMap_y A.g α.τ₂ β.τ₂ j k w₂ hpo
  let V : ShortComplex C := ShortComplex.mk j q hjq
  have hV : IsAdmissibleExact V :=
    isAdmissibleExact_pushoutQuotientMap A.g α.τ₂ β.τ₂ j k w₂ h₂ hpo
  let v : P ⟶ B.X₃ := hpo.desc α.τ₃ B.g α.comm₂₃.symm
  have hjv : j ≫ v = α.τ₃ := hpo.inl_desc _ _ _
  have hkv : k ≫ v = B.g := hpo.inr_desc _ _ _
  have hvq : v ≫ β.τ₃ = q ≫ Z.g := by
    apply hpo.hom_ext
    · rw [← Category.assoc, hjv, w₃, ← Category.assoc, hjq, zero_comp]
    · rw [← Category.assoc, hkv, ← β.comm₂₃, ← Category.assoc, hkq]
  let φ : V ⟶ C₃ := ShortComplex.homMk (𝟙 A.X₃) v Z.g
    (by
      change 𝟙 A.X₃ ≫ α.τ₃ = j ≫ v
      rw [Category.id_comp]
      exact hjv.symm) hvq
  have hφ₁ : φ.τ₁ = 𝟙 A.X₃ := rfl
  have hφIso : IsIso φ.τ₁ := by
    rw [hφ₁]
    simpa only [Iso.refl_hom] using (Iso.refl A.X₃).isIso_hom
  have hpb : IsPullback q v Z.g β.τ₃ :=
    isPullback_g_of_isAdmissibleExact_of_isIso_left φ hV hC₃
  have hv : IsAdmissibleEpi v :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := admissibleEpisOf C IsAdmissibleExact) hpb (isAdmissibleEpi_g hZ)
  have wk : (A.f ≫ α.τ₂) ≫ k = 0 := by
    rw [Category.assoc, ← hpo.w, ← Category.assoc, A.zero, zero_comp]
  have hK : IsAdmissibleExact (ShortComplex.mk (A.f ≫ α.τ₂) k wk) :=
    isAdmissibleExact_comp_pushout A.f A.g α.τ₂ β.τ₂ j k
      A.zero w₂ hA h₂ hpo
  let P₁ : AdmissibleEpiKernelPresentation k :=
    { kernel := A.X₁
      ι := A.f ≫ α.τ₂
      zero := wk
      exact := hK }
  let P₀ : AdmissibleEpiKernelPresentation Z.g :=
    { kernel := Z.X₁
      ι := Z.f
      zero := Z.zero
      exact := hZ }
  let Q : P₀.BaseChange β.τ₃ :=
    { obj := P
      fst := v
      snd := q
      square := hpb.flip
      fst_admissible := hv }
  let l : Z.X₁ ⟶ P := Q.kernelLift
  have hlq : l ≫ q = Z.f := Q.kernelLift_snd
  have hlv : l ≫ v = 0 := Q.kernelLift_fst
  have hL : IsAdmissibleExact (ShortComplex.mk l v hlv) :=
    Q.kernelPresentation.exact
  let P₂ : AdmissibleEpiKernelPresentation v :=
    { kernel := Z.X₁
      ι := l
      zero := hlv
      exact := hL }
  let R := P₁.compositeBaseChange P₂
  have hb : β.τ₁ ≫ l = B.f ≫ k := by
    apply hpb.hom_ext
    · rw [Category.assoc, hlq, Category.assoc, hkq, β.comm₁₂]
    · rw [Category.assoc, hlv, comp_zero, Category.assoc, hkv, B.zero]
  let θ : B.X₁ ⟶ R.obj := R.square.lift β.τ₁ B.f hb
  have hθfst : θ ≫ R.fst = β.τ₁ := R.square.lift_fst _ _ _
  have hθsnd : θ ≫ R.snd = B.f := R.square.lift_snd _ _ _
  have hαθ : α.τ₁ ≫ θ = R.kernelLift := by
    apply R.square.hom_ext
    · rw [Category.assoc, hθfst, w₁, R.kernelLift_fst]
    · rw [Category.assoc, hθsnd, α.comm₁₂, R.kernelLift_snd]
  let N : ShortComplex C := ShortComplex.mk R.kernelLift R.fst R.kernelLift_fst
  have hN : IsAdmissibleExact N := R.kernelPresentation.exact
  let ψ : C₁ ⟶ N := ShortComplex.homMk (𝟙 A.X₁) θ (𝟙 Z.X₁)
    (by
      change 𝟙 A.X₁ ≫ R.kernelLift = α.τ₁ ≫ θ
      rw [Category.id_comp]
      exact hαθ.symm)
    (by
      change θ ≫ R.fst = β.τ₁ ≫ 𝟙 Z.X₁
      rw [Category.comp_id]
      exact hθfst)
  have hψ₁ : ψ.τ₁ = 𝟙 A.X₁ := rfl
  have hψ₂ : ψ.τ₂ = θ := rfl
  have hψ₃ : ψ.τ₃ = 𝟙 Z.X₁ := rfl
  have hψIso₁ : IsIso ψ.τ₁ := by
    rw [hψ₁]
    simpa only [Iso.refl_hom] using (Iso.refl A.X₁).isIso_hom
  have hψIso₃ : IsIso ψ.τ₃ := by
    rw [hψ₃]
    simpa only [Iso.refl_hom] using (Iso.refl Z.X₁).isIso_hom
  have hψpb := isPullback_g_of_isAdmissibleExact_of_isIso_left ψ hC₁ hN
  have hθIso : IsIso θ := by
    have h : IsIso ψ.τ₂ := hψpb.isIso_snd_of_isIso hψIso₃
    simpa only [hψ₂] using h
  have wR : R.snd ≫ (k ≫ v) = 0 := by
    rw [← Category.assoc, ← R.square.w, Category.assoc, hlv, comp_zero]
  let H : ShortComplex C := ShortComplex.mk R.snd (k ≫ v) wR
  have hH : IsAdmissibleExact H := (P₁.composite P₂).exact
  let eB : B ≅ H :=
    ShortComplex.isoMk (asIso θ) (Iso.refl B.X₂) (Iso.refl B.X₃)
      (by
        change θ ≫ R.snd = B.f ≫ (Iso.refl B.X₂).hom
        rw [Iso.refl_hom, Category.comp_id]
        exact hθsnd)
      (by
        change (Iso.refl B.X₂).hom ≫ (k ≫ v) = B.g ≫ (Iso.refl B.X₃).hom
        simpa only [Iso.refl_hom, Category.id_comp, Category.comp_id] using hkv)
  exact isAdmissibleExact_of_iso eB.symm hH

end CategoryTheory.ExactCategory

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
public import MathlibExt.CategoryTheory.ExactCategory.KernelPullback

/-!
# The admissible three-by-three lemma

A short complex `D : ShortComplex (ShortComplex C)` records a commuting
three-by-three diagram whose rows and columns all have zero composite.
The rows are `D.X₁`, `D.X₂`, and `D.X₃`; projection images give the columns.
Admissible exactness of the columns and of the first two rows implies
admissible exactness of the last row in the chosen exact structure on `C`.

The proof constructs two pushouts. The comparison from the first pushout
to the middle row is an admissible mono by the common-left pullback square.
The second pushout produces the bottom row, whose middle object is then
identified with the given column quotient by the cokernel universal
property.
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
and the squares commute. If the three columns and the top and middle rows
are admissible exact, then the bottom row `D.X₃` is admissible exact.
A merely commuting grid without the short-complex data is not an input. -/
theorem isAdmissibleExact_bottom_of_three_by_three
    (D : ShortComplex (ShortComplex C))
    (hA : IsAdmissibleExact D.X₁) (hB : IsAdmissibleExact D.X₂)
    (h₁ : IsAdmissibleExact (D.map (ShortComplex.π₁ : ShortComplex C ⥤ C)))
    (h₂ : IsAdmissibleExact (D.map (ShortComplex.π₂ : ShortComplex C ⥤ C)))
    (h₃ : IsAdmissibleExact (D.map (ShortComplex.π₃ : ShortComplex C ⥤ C))) :
    IsAdmissibleExact D.X₃ := by
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
  let C₂ : ShortComplex C := ShortComplex.mk α.τ₂ β.τ₂ w₂
  have hC₂ : IsAdmissibleExact C₂ := h₂
  obtain ⟨P, j, k, hpo, _hj⟩ :=
    admissibleMono_pushout A.X₁ A.X₂ A.f (isAdmissibleMono_f hA)
      B.X₁ α.τ₁
  let q : P ⟶ A.X₃ :=
    pushoutQuotientMap α.τ₁ A.f A.g j k A.zero hpo
  have hjq : j ≫ q = 0 :=
    pushoutQuotientMap_x α.τ₁ A.f A.g j k A.zero hpo
  have hkq : k ≫ q = A.g :=
    pushoutQuotientMap_y α.τ₁ A.f A.g j k A.zero hpo
  let V : ShortComplex C := ShortComplex.mk j q hjq
  have hV : IsAdmissibleExact V :=
    isAdmissibleExact_pushoutQuotientMap α.τ₁ A.f A.g j k A.zero hA hpo
  let v : P ⟶ B.X₂ := hpo.desc B.f α.τ₂ α.comm₁₂
  have hjv : j ≫ v = B.f := hpo.inl_desc _ _ _
  have hkv : k ≫ v = α.τ₂ := hpo.inr_desc _ _ _
  have hvq : v ≫ B.g = q ≫ α.τ₃ := by
    apply hpo.hom_ext
    · rw [← Category.assoc, hjv, B.zero, ← Category.assoc, hjq, zero_comp]
    · rw [← Category.assoc, hkv, α.comm₂₃, ← Category.assoc, hkq]
  let φ : V ⟶ B := ShortComplex.homMk (𝟙 B.X₁) v α.τ₃
    (by
      change 𝟙 B.X₁ ≫ B.f = j ≫ v
      rw [Category.id_comp]
      exact hjv.symm) hvq
  have hφ₁ : φ.τ₁ = 𝟙 B.X₁ := rfl
  have hφIso : IsIso φ.τ₁ := by
    rw [hφ₁]
    simpa only [Iso.refl_hom] using (Iso.refl B.X₁).isIso_hom
  have hpb : IsPullback q v α.τ₃ B.g :=
    isPullback_g_of_isAdmissibleExact_of_isIso_left φ hV hB
  have wv : v ≫ (B.g ≫ β.τ₃) = 0 := by
    rw [← Category.assoc, hvq, Category.assoc, w₃, comp_zero]
  let V₂ : ShortComplex C := ShortComplex.mk v (B.g ≫ β.τ₃) wv
  have hV₂ : IsAdmissibleExact V₂ := by
    exact isAdmissibleExact_pullbackKernelSequence h₃ (isAdmissibleEpi_g hB) hpb
  let t : P ⟶ Z.X₁ :=
    pushoutQuotientMap A.f α.τ₁ β.τ₁ k j w₁ hpo.flip
  have hkt : k ≫ t = 0 :=
    pushoutQuotientMap_x A.f α.τ₁ β.τ₁ k j w₁ hpo.flip
  have hjt : j ≫ t = β.τ₁ :=
    pushoutQuotientMap_y A.f α.τ₁ β.τ₁ k j w₁ hpo.flip
  let L : ShortComplex C := ShortComplex.mk k t hkt
  have hL : IsAdmissibleExact L :=
    isAdmissibleExact_pushoutQuotientMap A.f α.τ₁ β.τ₁ k j w₁ h₁ hpo.flip
  obtain ⟨Q, u, w, hpo₂, _hu⟩ :=
    admissibleMono_pushout P B.X₂ v (isAdmissibleMono_f hV₂) Z.X₁ t
  have hcomp := isAdmissibleExact_comp_pushout k t v (B.g ≫ β.τ₃) u w
    hkt wv hL hV₂ hpo₂
  have wα : α.τ₂ ≫ w = 0 := by
    rw [← hkv, Category.assoc, ← hpo₂.w, ← Category.assoc, hkt, zero_comp]
  let M : ShortComplex C := ShortComplex.mk α.τ₂ w wα
  have hM : IsAdmissibleExact M := by
    simpa only [M, hkv] using hcomp
  let hcQ : IsColimit (CokernelCofork.ofπ w wα) :=
    isColimit_cokernelCofork_of_isAdmissibleExact hM
  let hcZ : IsColimit (CokernelCofork.ofπ β.τ₂ w₂) :=
    isColimit_cokernelCofork_of_isAdmissibleExact hC₂
  let e : Q ≅ Z.X₂ := hcQ.coconePointUniqueUpToIso hcZ
  have he : w ≫ e.hom = β.τ₂ := by
    have h := IsColimit.comp_coconePointUniqueUpToIso_hom hcQ hcZ
      WalkingParallelPair.one
    simpa only [Cofork.app_one_eq_π, CokernelCofork.π_ofπ] using h
  let n : Q ⟶ Z.X₃ :=
    pushoutQuotientMap t v (B.g ≫ β.τ₃) u w wv hpo₂
  have hun : u ≫ n = 0 :=
    pushoutQuotientMap_x t v (B.g ≫ β.τ₃) u w wv hpo₂
  have hwn : w ≫ n = B.g ≫ β.τ₃ :=
    pushoutQuotientMap_y t v (B.g ≫ β.τ₃) u w wv hpo₂
  let N : ShortComplex C := ShortComplex.mk u n hun
  have hN : IsAdmissibleExact N :=
    isAdmissibleExact_pushoutQuotientMap t v (B.g ≫ β.τ₃) u w wv hV₂ hpo₂
  have hue : u ≫ e.hom = Z.f := by
    have hEpiβ : Epi β.τ₁ := (isAdmissibleEpi_g h₁).epi
    apply (cancel_epi β.τ₁).mp
    calc
      β.τ₁ ≫ (u ≫ e.hom) = (j ≫ t) ≫ (u ≫ e.hom) := by rw [hjt]
      _ = j ≫ ((t ≫ u) ≫ e.hom) := by simp only [Category.assoc]
      _ = j ≫ ((v ≫ w) ≫ e.hom) := by rw [hpo₂.w]
      _ = (j ≫ v) ≫ (w ≫ e.hom) := by simp only [Category.assoc]
      _ = B.f ≫ β.τ₂ := by rw [hjv, he]
      _ = β.τ₁ ≫ Z.f := β.comm₁₂.symm
  have heg : e.hom ≫ Z.g = n := by
    have hEpiw : Epi w := (isAdmissibleEpi_g hM).epi
    apply (cancel_epi w).mp
    calc
      w ≫ (e.hom ≫ Z.g) = (w ≫ e.hom) ≫ Z.g := (Category.assoc _ _ _).symm
      _ = β.τ₂ ≫ Z.g := by rw [he]
      _ = B.g ≫ β.τ₃ := β.comm₂₃
      _ = w ≫ n := hwn.symm
  let rowIso : N ≅ Z :=
    ShortComplex.isoMk (Iso.refl Z.X₁) e (Iso.refl Z.X₃)
      (by
        change (Iso.refl Z.X₁).hom ≫ Z.f = u ≫ e.hom
        simpa only [Iso.refl_hom, Category.id_comp] using hue.symm)
      (by
        change e.hom ≫ Z.g = n ≫ (Iso.refl Z.X₃).hom
        simpa only [Iso.refl_hom, Category.comp_id] using heg)
  exact isAdmissibleExact_of_iso rowIso hN

end CategoryTheory.ExactCategory

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# Composition of complex-shape embeddings

Zero extension along a composite embedding of complex shapes agrees with
successive zero extensions. The component comparisons agree on the image
of the composite; outside that image the terms are zero objects.
-/

@[expose] public section
noncomputable section

open CategoryTheory Category Limits

universe w₀ w₁ w₂ u v

variable {I₀ : Type w₀} {I₁ : Type w₁} {I₂ : Type w₂}
  {c₀ : ComplexShape I₀} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

namespace ComplexShape.Embedding

/-- Compose the injective index maps and their native relation proofs. -/
def comp (e₁ : (c₀).Embedding c₁) (e₂ : (c₁).Embedding c₂) : (c₀).Embedding c₂ where
  f i := e₂.f (e₁.f i)
  injective_f := e₂.injective_f.comp e₁.injective_f
  rel h := e₂.rel (e₁.rel h)

/-- The composite index is the successive index. -/
@[simp]
lemma comp_f (e₁ : (c₀).Embedding c₁) (e₂ : (c₁).Embedding c₂) (i : I₀) :
    (e₁.comp e₂).f i = e₂.f (e₁.f i) := rfl

end ComplexShape.Embedding

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  (K : HomologicalComplex C c₀) (e₁ : (c₀).Embedding c₁) (e₂ : (c₁).Embedding c₂)

/-- On a composite-image point, the two native extension coordinates recover the original
source object. -/
def extendCompSourceXIso (i₀ : I₀) (i₂ : I₂) (hi : e₂.f (e₁.f i₀) = i₂) :
    ((K.extend e₁).extend e₂).X i₂ ≅ K.X i₀ :=
  (K.extend e₁).extendXIso e₂ hi ≪≫
    K.extendXIso e₁ (show e₁.f i₀ = e₁.f i₀ from rfl)

/-- Both native extension differentials recover the original differential. -/
@[reassoc]
theorem extendCompSourceXIso_comm (i₀ j₀ : I₀) (i₂ j₂ : I₂)
    (hi : e₂.f (e₁.f i₀) = i₂) (hj : e₂.f (e₁.f j₀) = j₂) :
    (extendCompSourceXIso K e₁ e₂ i₀ i₂ hi).hom ≫ K.d i₀ j₀ =
      ((K.extend e₁).extend e₂).d i₂ j₂ ≫
        (extendCompSourceXIso K e₁ e₂ j₀ j₂ hj).hom := by
  let aᵢ := (K.extend e₁).extendXIso e₂ hi
  let aⱼ := (K.extend e₁).extendXIso e₂ hj
  let bᵢ := K.extendXIso e₁ (show e₁.f i₀ = e₁.f i₀ from rfl)
  let bⱼ := K.extendXIso e₁ (show e₁.f j₀ = e₁.f j₀ from rfl)
  change (aᵢ.hom ≫ bᵢ.hom) ≫ K.d i₀ j₀ =
    ((K.extend e₁).extend e₂).d i₂ j₂ ≫ aⱼ.hom ≫ bⱼ.hom
  rw [(K.extend e₁).extend_d_eq e₂ hi hj,
    K.extend_d_eq e₁ (show e₁.f i₀ = e₁.f i₀ from rfl)
      (show e₁.f j₀ = e₁.f j₀ from rfl)]
  simp only [Category.assoc]
  change aᵢ.hom ≫ bᵢ.hom ≫ K.d i₀ j₀ =
    aᵢ.hom ≫ bᵢ.hom ≫ K.d i₀ j₀ ≫ bⱼ.inv ≫ aⱼ.inv ≫ aⱼ.hom ≫ bⱼ.hom
  rw [aⱼ.inv_hom_id_assoc bⱼ.hom, bⱼ.inv_hom_id, Category.comp_id]

/-- The double extension is zero outside the composite image, including points in
the second image whose intermediate preimage lies outside the first image. -/
theorem isZero_extendExtend_X_of_notMem (i₂ : I₂)
    (hi₂ : ∀ i₀, e₂.f (e₁.f i₀) ≠ i₂) :
    IsZero (((K.extend e₁).extend e₂).X i₂) := by
  by_cases h₂ : ∃ i₁, e₂.f i₁ = i₂
  · obtain ⟨i₁, h₂⟩ := h₂
    have hZero : IsZero ((K.extend e₁).X i₁) := K.isZero_extend_X e₁ i₁ (by
      intro i₀ h₁
      apply hi₂ i₀
      exact (congrArg e₂.f h₁).trans h₂)
    exact hZero.of_iso ((K.extend e₁).extendXIso e₂ h₂)
  · exact (K.extend e₁).isZero_extend_X e₂ i₂ (by
      simpa only [not_exists] using h₂)

variable (e₃ : (c₀).Embedding c₂) (hf : ∀ i₀, e₂.f (e₁.f i₀) = e₃.f i₀)

/-- The object comparison with an embedding whose index map is the composite.
The supplied equation identifies only indices; all comparison data are constructed. -/
def extendCompXIsoOfEq (i₂ : I₂) :
    ((K.extend e₁).extend e₂).X i₂ ≅ (K.extend e₃).X i₂ := by
  classical
  by_cases hi : ∃ i₀, e₃.f i₀ = i₂
  · exact extendCompSourceXIso K e₁ e₂ hi.choose i₂
      ((hf hi.choose).trans hi.choose_spec) ≪≫ (K.extendXIso e₃ hi.choose_spec).symm
  · have hZero₁ : IsZero (((K.extend e₁).extend e₂).X i₂) :=
      isZero_extendExtend_X_of_notMem K e₁ e₂ i₂ (by
        intro i₀ h
        exact hi ⟨i₀, (hf i₀).symm.trans h⟩)
    have hZero₂ : IsZero ((K.extend e₃).X i₂) := K.isZero_extend_X e₃ i₂ (by
      simpa only [not_exists] using hi)
    exact hZero₁.iso hZero₂

/-- The composite-image value is independent of the chosen preimage and keeps the native target coordinate. -/
lemma extendCompXIsoOfEq_of_mem (i₀ : I₀) (i₂ : I₂) (hi : e₃.f i₀ = i₂) :
    extendCompXIsoOfEq K e₁ e₂ e₃ hf i₂ =
      extendCompSourceXIso K e₁ e₂ i₀ i₂ ((hf i₀).trans hi) ≪≫
        (K.extendXIso e₃ hi).symm := by
  unfold extendCompXIsoOfEq
  split
  next h =>
    have hChoose : h.choose = i₀ := e₃.injective_f (h.choose_spec.trans hi.symm)
    cases hChoose
    rfl
  next h => exact (h ⟨i₀, hi⟩).elim

/-- The constructed comparison commutes with the native differentials. -/
theorem extendCompXIsoOfEq_comm (i₂ j₂ : I₂) :
    (extendCompXIsoOfEq K e₁ e₂ e₃ hf i₂).hom ≫ (K.extend e₃).d i₂ j₂ =
      ((K.extend e₁).extend e₂).d i₂ j₂ ≫
        (extendCompXIsoOfEq K e₁ e₂ e₃ hf j₂).hom := by
  by_cases hi : ∃ i₀, e₃.f i₀ = i₂
  · obtain ⟨i₀, hi⟩ := hi
    by_cases hj : ∃ j₀, e₃.f j₀ = j₂
    · obtain ⟨j₀, hj⟩ := hj
      let aᵢ := extendCompSourceXIso K e₁ e₂ i₀ i₂ ((hf i₀).trans hi)
      let aⱼ := extendCompSourceXIso K e₁ e₂ j₀ j₂ ((hf j₀).trans hj)
      let bᵢ := K.extendXIso e₃ hi
      let bⱼ := K.extendXIso e₃ hj
      have hOriginal : aᵢ.hom ≫ K.d i₀ j₀ =
          ((K.extend e₁).extend e₂).d i₂ j₂ ≫ aⱼ.hom :=
        extendCompSourceXIso_comm K e₁ e₂ i₀ j₀ i₂ j₂
          ((hf i₀).trans hi) ((hf j₀).trans hj)
      rw [extendCompXIsoOfEq_of_mem K e₁ e₂ e₃ hf i₀ i₂ hi,
        extendCompXIsoOfEq_of_mem K e₁ e₂ e₃ hf j₀ j₂ hj]
      change (aᵢ.hom ≫ bᵢ.inv) ≫ (K.extend e₃).d i₂ j₂ =
        ((K.extend e₁).extend e₂).d i₂ j₂ ≫ aⱼ.hom ≫ bⱼ.inv
      rw [K.extend_d_eq e₃ hi hj]
      simp only [Category.assoc]
      change aᵢ.hom ≫ bᵢ.inv ≫ bᵢ.hom ≫ K.d i₀ j₀ ≫ bⱼ.inv =
        ((K.extend e₁).extend e₂).d i₂ j₂ ≫ aⱼ.hom ≫ bⱼ.inv
      rw [bᵢ.inv_hom_id_assoc (K.d i₀ j₀ ≫ bⱼ.inv)]
      simpa only [Category.assoc] using congrArg (fun f => f ≫ bⱼ.inv) hOriginal
    · have hZero : IsZero ((K.extend e₃).X j₂) := K.isZero_extend_X e₃ j₂ (by
        simpa only [not_exists] using hj)
      exact hZero.eq_of_tgt _ _
  · have hZero : IsZero (((K.extend e₁).extend e₂).X i₂) :=
      isZero_extendExtend_X_of_notMem K e₁ e₂ i₂ (by
        intro i₀ h
        exact hi ⟨i₀, (hf i₀).symm.trans h⟩)
    exact hZero.eq_of_src _ _

/-- The double native zero extension is the zero extension along the composite index map.
No desired isomorphism, reflection or support premise is assumed. -/
def extendCompIsoOfEq : (K.extend e₁).extend e₂ ≅ K.extend e₃ :=
  Hom.isoOfComponents (extendCompXIsoOfEq K e₁ e₂ e₃ hf)
    (fun i₂ j₂ _ => extendCompXIsoOfEq_comm K e₁ e₂ e₃ hf i₂ j₂)

/-- The computed chain comparison retains both original native extension coordinates. -/
lemma extendCompIsoOfEq_hom_f (i₀ : I₀) (i₂ : I₂) (hi : e₃.f i₀ = i₂) :
    (extendCompIsoOfEq K e₁ e₂ e₃ hf).hom.f i₂ =
      (extendCompSourceXIso K e₁ e₂ i₀ i₂ ((hf i₀).trans hi)).hom ≫
        (K.extendXIso e₃ hi).inv := by
  change (extendCompXIsoOfEq K e₁ e₂ e₃ hf i₂).hom = _
  rw [extendCompXIsoOfEq_of_mem K e₁ e₂ e₃ hf i₀ i₂ hi]
  rfl

/-- The inverse comparison retains the original coordinates in reverse order. -/
lemma extendCompIsoOfEq_inv_f (i₀ : I₀) (i₂ : I₂) (hi : e₃.f i₀ = i₂) :
    (extendCompIsoOfEq K e₁ e₂ e₃ hf).inv.f i₂ =
      (K.extendXIso e₃ hi).hom ≫
        (extendCompSourceXIso K e₁ e₂ i₀ i₂ ((hf i₀).trans hi)).inv := by
  change (extendCompXIsoOfEq K e₁ e₂ e₃ hf i₂).inv = _
  rw [extendCompXIsoOfEq_of_mem K e₁ e₂ e₃ hf i₀ i₂ hi]
  rfl

variable {K} {L : HomologicalComplex C c₀}

/-- Successive native coordinates commute with an actual original complex map. -/
@[reassoc]
theorem extendCompSourceXIso_hom_naturality (φ : K ⟶ L) (i₀ : I₀) (i₂ : I₂)
    (hi : e₂.f (e₁.f i₀) = i₂) :
    (extendMap (extendMap φ e₁) e₂).f i₂ ≫
        (extendCompSourceXIso L e₁ e₂ i₀ i₂ hi).hom =
      (extendCompSourceXIso K e₁ e₂ i₀ i₂ hi).hom ≫ φ.f i₀ := by
  let aK := (K.extend e₁).extendXIso e₂ hi
  let aL := (L.extend e₁).extendXIso e₂ hi
  let bK := K.extendXIso e₁ (show e₁.f i₀ = e₁.f i₀ from rfl)
  let bL := L.extendXIso e₁ (show e₁.f i₀ = e₁.f i₀ from rfl)
  have hOuter : (extendMap (extendMap φ e₁) e₂).f i₂ ≫ aL.hom =
      aK.hom ≫ (extendMap φ e₁).f (e₁.f i₀) :=
    (e₂.extendFunctorCompEvalIso C hi).hom.naturality (extendMap φ e₁)
  have hInner : (extendMap φ e₁).f (e₁.f i₀) ≫ bL.hom = bK.hom ≫ φ.f i₀ :=
    (e₁.extendFunctorCompEvalIso C (show e₁.f i₀ = e₁.f i₀ from rfl)).hom.naturality φ
  change (extendMap (extendMap φ e₁) e₂).f i₂ ≫ (aL.hom ≫ bL.hom) =
    (aK.hom ≫ bK.hom) ≫ φ.f i₀
  calc
    (extendMap (extendMap φ e₁) e₂).f i₂ ≫ (aL.hom ≫ bL.hom) =
        ((extendMap (extendMap φ e₁) e₂).f i₂ ≫ aL.hom) ≫ bL.hom :=
      (Category.assoc _ _ _).symm
    _ = (aK.hom ≫ (extendMap φ e₁).f (e₁.f i₀)) ≫ bL.hom := by rw [hOuter]
    _ = aK.hom ≫ ((extendMap φ e₁).f (e₁.f i₀) ≫ bL.hom) := Category.assoc _ _ _
    _ = aK.hom ≫ (bK.hom ≫ φ.f i₀) := by rw [hInner]
    _ = (aK.hom ≫ bK.hom) ≫ φ.f i₀ := (Category.assoc _ _ _).symm

/-- The double-extension comparison is natural in the original complex map. -/
@[reassoc]
theorem extendCompIsoOfEq_hom_naturality (φ : K ⟶ L) :
    extendMap (extendMap φ e₁) e₂ ≫ (extendCompIsoOfEq L e₁ e₂ e₃ hf).hom =
      (extendCompIsoOfEq K e₁ e₂ e₃ hf).hom ≫ extendMap φ e₃ := by
  apply HomologicalComplex.hom_ext
  intro i₂
  change (extendMap (extendMap φ e₁) e₂).f i₂ ≫
      (extendCompIsoOfEq L e₁ e₂ e₃ hf).hom.f i₂ =
    (extendCompIsoOfEq K e₁ e₂ e₃ hf).hom.f i₂ ≫ (extendMap φ e₃).f i₂
  by_cases hi : ∃ i₀, e₃.f i₀ = i₂
  · obtain ⟨i₀, hi⟩ := hi
    let aK := extendCompSourceXIso K e₁ e₂ i₀ i₂ ((hf i₀).trans hi)
    let aL := extendCompSourceXIso L e₁ e₂ i₀ i₂ ((hf i₀).trans hi)
    let bK := K.extendXIso e₃ hi
    let bL := L.extendXIso e₃ hi
    have hSource : (extendMap (extendMap φ e₁) e₂).f i₂ ≫ aL.hom =
        aK.hom ≫ φ.f i₀ :=
      extendCompSourceXIso_hom_naturality e₁ e₂ φ i₀ i₂ ((hf i₀).trans hi)
    have hTarget : φ.f i₀ ≫ bL.inv = bK.inv ≫ (extendMap φ e₃).f i₂ :=
      (e₃.extendFunctorCompEvalIso C hi).inv.naturality φ
    rw [extendCompIsoOfEq_hom_f L e₁ e₂ e₃ hf i₀ i₂ hi,
      extendCompIsoOfEq_hom_f K e₁ e₂ e₃ hf i₀ i₂ hi]
    change (extendMap (extendMap φ e₁) e₂).f i₂ ≫ (aL.hom ≫ bL.inv) =
      (aK.hom ≫ bK.inv) ≫ (extendMap φ e₃).f i₂
    calc
      (extendMap (extendMap φ e₁) e₂).f i₂ ≫ (aL.hom ≫ bL.inv) =
          ((extendMap (extendMap φ e₁) e₂).f i₂ ≫ aL.hom) ≫ bL.inv :=
        (Category.assoc _ _ _).symm
      _ = (aK.hom ≫ φ.f i₀) ≫ bL.inv := by rw [hSource]
      _ = aK.hom ≫ (φ.f i₀ ≫ bL.inv) := Category.assoc _ _ _
      _ = aK.hom ≫ (bK.inv ≫ (extendMap φ e₃).f i₂) := by rw [hTarget]
      _ = (aK.hom ≫ bK.inv) ≫ (extendMap φ e₃).f i₂ := (Category.assoc _ _ _).symm
  · have hZero : IsZero (((K.extend e₁).extend e₂).X i₂) :=
      isZero_extendExtend_X_of_notMem K e₁ e₂ i₂ (by
        intro i₀ h
        exact hi ⟨i₀, (hf i₀).symm.trans h⟩)
    exact hZero.eq_of_src _ _

variable (K)

/-- Extend by two arbitrary shape embeddings, or by their actual composite. -/
def extendCompIso : (K.extend e₁).extend e₂ ≅ K.extend (e₁.comp e₂) :=
  extendCompIsoOfEq K e₁ e₂ (e₁.comp e₂) (fun _ => rfl)

/-- The canonical composite-extension comparison is natural in every original map. -/
@[reassoc]
theorem extendCompIso_hom_naturality (φ : K ⟶ L) :
    extendMap (extendMap φ e₁) e₂ ≫ (extendCompIso L e₁ e₂).hom =
      (extendCompIso K e₁ e₂).hom ≫ extendMap φ (e₁.comp e₂) :=
  extendCompIsoOfEq_hom_naturality e₁ e₂ (e₁.comp e₂) (fun _ => rfl) φ

end HomologicalComplex

namespace ComplexShape.Embedding

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- Successive native extension functors are naturally isomorphic to the composite
extension functor, for arbitrary index worlds and shape embeddings. -/
def extendFunctorCompIso (e₁ : (c₀).Embedding c₁) (e₂ : (c₁).Embedding c₂) :
    e₁.extendFunctor C ⋙ e₂.extendFunctor C ≅ (e₁.comp e₂).extendFunctor C :=
  NatIso.ofComponents (fun K => HomologicalComplex.extendCompIso K e₁ e₂)
    (by
      intro K L φ
      exact HomologicalComplex.extendCompIso_hom_naturality K e₁ e₂ φ)

end ComplexShape.Embedding

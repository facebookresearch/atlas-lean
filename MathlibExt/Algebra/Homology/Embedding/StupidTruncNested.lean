/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Embedding.StupidTruncInclusion

/-!
# Maps between nested stupid truncations

If the support of one complex-shape embedding is contained in that of
another, the corresponding stupid truncation is canonically a subcomplex of
the larger stupid truncation.  The resulting map is characterized by its
factorization through the canonical inclusions into the original complex.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

variable {ι₁ ι₂ ι : Type*}
variable {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}
  {c : ComplexShape ι}

namespace ComplexShape.Embedding

/-- The ambient support of `e₁` is contained in the ambient support of `e₂`. -/
def RangeLE (e₁ : c₁.Embedding c) (e₂ : c₂.Embedding c) : Prop :=
  Set.range e₁.f ⊆ Set.range e₂.f

namespace RangeLE

/-- Every embedding support contains itself. -/
protected theorem refl (e : c₁.Embedding c) : e.RangeLE e :=
  Set.Subset.rfl

/-- Support containment is transitive. -/
protected theorem trans {ι₃ : Type*} {c₃ : ComplexShape ι₃}
    {e₁ : c₁.Embedding c} {e₂ : c₂.Embedding c}
    {e₃ : c₃.Embedding c} (h₁₂ : e₁.RangeLE e₂)
    (h₂₃ : e₂.RangeLE e₃) : e₁.RangeLE e₃ :=
  Set.Subset.trans h₁₂ h₂₃

end RangeLE

end ComplexShape.Embedding

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
variable (K L : HomologicalComplex C c)
variable (e₁ : c₁.Embedding c) (e₂ : c₂.Embedding c)

namespace stupidTruncMapOfRangeLE

variable [e₁.IsRelIff] [e₂.IsRelIff]
variable (h : e₁.RangeLE e₂)

open scoped Classical in
/-- Components of the canonical map between nested stupid truncations. -/
noncomputable def f (k : ι) :
    (K.stupidTrunc e₁).X k ⟶ (K.stupidTrunc e₂).X k :=
  if hk : ∃ i, e₁.f i = k then
    (K.stupidTruncXIso e₁ hk.choose_spec).hom ≫
      (K.stupidTruncXIso e₂ (h hk).choose_spec).inv
  else 0

/-- On the smaller support, the nested map is the composite of the two
canonical coordinate isomorphisms. -/
lemma f_eq {i₁ : ι₁} {i₂ : ι₂} {k : ι}
    (hi₁ : e₁.f i₁ = k) (hi₂ : e₂.f i₂ = k) :
    f K e₁ e₂ h k =
      (K.stupidTruncXIso e₁ hi₁).hom ≫
        (K.stupidTruncXIso e₂ hi₂).inv := by
  have hk : ∃ i, e₁.f i = k := ⟨i₁, hi₁⟩
  have hsource : hk.choose = i₁ :=
    e₁.injective_f (hk.choose_spec.trans hi₁.symm)
  have htarget : (h hk).choose = i₂ :=
    e₂.injective_f ((h hk).choose_spec.trans hi₂.symm)
  simp only [f, dite_eq_left hk]
  subst i₁
  subst i₂
  rfl

/-- Off the smaller support, the nested map component is zero. -/
lemma f_eq_zero (k : ι) (hk : ∀ i, e₁.f i ≠ k) :
    f K e₁ e₂ h k = 0 := by
  rw [f, dite_eq_right]
  simpa only [not_exists] using hk

end stupidTruncMapOfRangeLE

namespace stupidTruncMapOfRangeLE

variable [e₁.IsTruncGE] [e₂.IsRelIff]
variable (h : e₁.RangeLE e₂)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma comm (k l : ι) :
    f K e₁ e₂ h k ≫ (K.stupidTrunc e₂).d k l =
      (K.stupidTrunc e₁).d k l ≫ f K e₁ e₂ h l := by
  by_cases hkl : c.Rel k l
  · by_cases hk : ∃ i, e₁.f i = k
    · obtain ⟨i, hi⟩ := hk
      subst k
      obtain ⟨j, hj⟩ := e₁.mem_next hkl
      obtain ⟨i₂, hi₂⟩ := h ⟨i, rfl⟩
      obtain ⟨j₂, hj₂⟩ := h ⟨j, hj⟩
      rw [f_eq K e₁ e₂ h rfl hi₂, f_eq K e₁ e₂ h hj hj₂,
        stupidTrunc_d_eq K e₂ hi₂ hj₂, stupidTrunc_d_eq K e₁ rfl hj]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    · have hzero := K.isZero_stupidTrunc_X e₁ k (by simpa using hk)
      exact hzero.eq_of_src _ _
  · rw [(K.stupidTrunc e₁).shape _ _ hkl,
      (K.stupidTrunc e₂).shape _ _ hkl, comp_zero, zero_comp]

end stupidTruncMapOfRangeLE

/-- The canonical map from a stupid truncation into a larger stupid
truncation of the same complex. -/
noncomputable def stupidTruncMapOfRangeLE
    [e₁.IsTruncGE] [e₂.IsRelIff] (h : e₁.RangeLE e₂) :
    K.stupidTrunc e₁ ⟶ K.stupidTrunc e₂ where
  f k := stupidTruncMapOfRangeLE.f K e₁ e₂ h k
  comm' k l _ := stupidTruncMapOfRangeLE.comm K e₁ e₂ h k l

/-- On the smaller support, the canonical nested map is the composite of the
two stupid-truncation coordinate isomorphisms. -/
@[simp]
lemma stupidTruncMapOfRangeLE_f
    [e₁.IsTruncGE] [e₂.IsRelIff] (h : e₁.RangeLE e₂)
    {i₁ : ι₁} {i₂ : ι₂} {k : ι}
    (hi₁ : e₁.f i₁ = k) (hi₂ : e₂.f i₂ = k) :
    (K.stupidTruncMapOfRangeLE e₁ e₂ h).f k =
      (K.stupidTruncXIso e₁ hi₁).hom ≫
        (K.stupidTruncXIso e₂ hi₂).inv :=
  stupidTruncMapOfRangeLE.f_eq K e₁ e₂ h hi₁ hi₂

/-- Off the smaller support, the canonical nested map component is zero. -/
lemma stupidTruncMapOfRangeLE_f_eq_zero
    [e₁.IsTruncGE] [e₂.IsRelIff] (h : e₁.RangeLE e₂)
    (k : ι) (hk : ∀ i, e₁.f i ≠ k) :
    (K.stupidTruncMapOfRangeLE e₁ e₂ h).f k = 0 :=
  stupidTruncMapOfRangeLE.f_eq_zero K e₁ e₂ h k hk

instance stupidTruncMapOfRangeLE_f_mono
    [e₁.IsTruncGE] [e₂.IsRelIff] (h : e₁.RangeLE e₂) (k : ι) :
    Mono ((K.stupidTruncMapOfRangeLE e₁ e₂ h).f k) := by
  by_cases hk : ∃ i, e₁.f i = k
  · obtain ⟨i, hi⟩ := hk
    obtain ⟨j, hj⟩ := h ⟨i, hi⟩
    rw [stupidTruncMapOfRangeLE_f K e₁ e₂ h hi hj]
    infer_instance
  · have hzero := K.isZero_stupidTrunc_X e₁ k (by simpa using hk)
    exact hzero.mono _

instance stupidTruncMapOfRangeLE_mono
    [e₁.IsTruncGE] [e₂.IsRelIff] (h : e₁.RangeLE e₂) :
    Mono (K.stupidTruncMapOfRangeLE e₁ e₂ h) :=
  HomologicalComplex.mono_of_mono_f _ fun k =>
    K.stupidTruncMapOfRangeLE_f_mono e₁ e₂ h k

/-- The nested truncation map followed by the larger inclusion is the smaller
inclusion. -/
@[reassoc (attr := simp)]
theorem stupidTruncMapOfRangeLE_ιStupidTrunc
    [e₁.IsTruncGE] [e₂.IsTruncGE] (h : e₁.RangeLE e₂) :
    K.stupidTruncMapOfRangeLE e₁ e₂ h ≫ K.ιStupidTrunc e₂ =
      K.ιStupidTrunc e₁ := by
  ext k
  by_cases hk : ∃ i, e₁.f i = k
  · obtain ⟨i, hi⟩ := hk
    obtain ⟨j, hj⟩ := h ⟨i, hi⟩
    simp only [HomologicalComplex.comp_f,
      stupidTruncMapOfRangeLE_f K e₁ e₂ h hi hj,
      ιStupidTrunc_f K e₂ k, ιStupidTrunc_f K e₁ k,
      stupidTruncι.f_eq K e₂ hj, stupidTruncι.f_eq K e₁ hi,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · have hzero := K.isZero_stupidTrunc_X e₁ k (by simpa using hk)
    exact hzero.eq_of_src _ _

/-- A nested truncation map from a support to itself is the identity. -/
@[simp]
theorem stupidTruncMapOfRangeLE_refl
    (e : c₁.Embedding c) [e.IsTruncGE] :
    K.stupidTruncMapOfRangeLE e e (ComplexShape.Embedding.RangeLE.refl e) =
      𝟙 _ := by
  apply (cancel_mono (K.ιStupidTrunc e)).1
  rw [stupidTruncMapOfRangeLE_ιStupidTrunc, Category.id_comp]

/-- Canonical maps between nested stupid truncations compose. -/
@[reassoc]
theorem stupidTruncMapOfRangeLE_comp
    {ι₃ : Type*} {c₃ : ComplexShape ι₃}
    (e₃ : c₃.Embedding c) [e₁.IsTruncGE] [e₂.IsTruncGE]
    [e₃.IsTruncGE] (h₁₂ : e₁.RangeLE e₂) (h₂₃ : e₂.RangeLE e₃) :
    K.stupidTruncMapOfRangeLE e₁ e₂ h₁₂ ≫
        K.stupidTruncMapOfRangeLE e₂ e₃ h₂₃ =
      K.stupidTruncMapOfRangeLE e₁ e₃ (h₁₂.trans h₂₃) := by
  apply (cancel_mono (K.ιStupidTrunc e₃)).1
  simp only [Category.assoc, stupidTruncMapOfRangeLE_ιStupidTrunc]

variable {K L}

/-- Canonical maps between nested stupid truncations are natural in the
original homological complex. -/
@[reassoc]
theorem stupidTruncMap_stupidTruncMapOfRangeLE_naturality
    [e₁.IsTruncGE] [e₂.IsTruncGE] (h : e₁.RangeLE e₂) (φ : K ⟶ L) :
    stupidTruncMap φ e₁ ≫ L.stupidTruncMapOfRangeLE e₁ e₂ h =
      K.stupidTruncMapOfRangeLE e₁ e₂ h ≫ stupidTruncMap φ e₂ := by
  apply (cancel_mono (L.ιStupidTrunc e₂)).1
  calc
    (stupidTruncMap φ e₁ ≫ L.stupidTruncMapOfRangeLE e₁ e₂ h) ≫
          L.ιStupidTrunc e₂ =
        stupidTruncMap φ e₁ ≫
          (L.stupidTruncMapOfRangeLE e₁ e₂ h ≫
            L.ιStupidTrunc e₂) := Category.assoc _ _ _
    _ = stupidTruncMap φ e₁ ≫ L.ιStupidTrunc e₁ := by
      rw [stupidTruncMapOfRangeLE_ιStupidTrunc]
    _ = K.ιStupidTrunc e₁ ≫ φ :=
      stupidTruncMap_ιStupidTrunc_naturality e₁ φ
    _ = (K.stupidTruncMapOfRangeLE e₁ e₂ h ≫
          K.ιStupidTrunc e₂) ≫ φ := by
      rw [stupidTruncMapOfRangeLE_ιStupidTrunc]
    _ = K.stupidTruncMapOfRangeLE e₁ e₂ h ≫
          (K.ιStupidTrunc e₂ ≫ φ) := Category.assoc _ _ _
    _ = K.stupidTruncMapOfRangeLE e₁ e₂ h ≫
          (stupidTruncMap φ e₂ ≫ L.ιStupidTrunc e₂) := by
      rw [stupidTruncMap_ιStupidTrunc_naturality]
    _ = (K.stupidTruncMapOfRangeLE e₁ e₂ h ≫
          stupidTruncMap φ e₂) ≫ L.ιStupidTrunc e₂ :=
      (Category.assoc _ _ _).symm

end HomologicalComplex

end

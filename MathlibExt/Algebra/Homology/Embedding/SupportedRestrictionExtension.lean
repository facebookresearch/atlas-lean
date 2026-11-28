/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Embedding.StupidTruncInclusion

/-!
# Reconstruction of supported homological complexes

Restricting a homological complex to a complex-shape embedding and
extending by zero reconstructs it when its terms outside the image are zero.
The component isomorphisms are natural and agree with the image and
off-image coordinates.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe w₁ w₂ v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {I : Type w₁} {J : Type w₂}
variable {c : ComplexShape I} {d : ComplexShape J}
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C]
variable (K : HomologicalComplex C d) (e : c.Embedding d) [e.IsRelIff]

/-- The component isomorphism from restriction followed by zero extension to
a complex strictly supported on the embedding range. -/
noncomputable def restrictExtendXIsoOfIsStrictlySupported
    [K.IsStrictlySupported e] (j : J) :
    (K.stupidTrunc e).X j ≅ K.X j := by
  by_cases hj : ∃ i, e.f i = j
  · exact K.stupidTruncXIso e hj.choose_spec
  · exact IsZero.iso
      (K.isZero_stupidTrunc_X e j (by simpa only [not_exists] using hj))
      (K.isZero_X_of_isStrictlySupported e j
        (by simpa only [not_exists] using hj))

/-- On the embedding range, the forward supported reconstruction component
is the native stupid-truncation component. -/
theorem restrictExtendXIsoOfIsStrictlySupported_hom
    [K.IsStrictlySupported e] {i : I} {j : J} (h : e.f i = j) :
    (restrictExtendXIsoOfIsStrictlySupported K e j).hom =
      (K.stupidTruncXIso e h).hom := by
  unfold restrictExtendXIsoOfIsStrictlySupported
  split
  next hj =>
    have hchoose : hj.choose = i :=
      e.injective_f (hj.choose_spec.trans h.symm)
    cases hchoose
    rfl
  next hj => exact (hj ⟨i, h⟩).elim

/-- On the embedding range, the inverse supported reconstruction component
is the inverse native stupid-truncation component. -/
theorem restrictExtendXIsoOfIsStrictlySupported_inv
    [K.IsStrictlySupported e] {i : I} {j : J} (h : e.f i = j) :
    (restrictExtendXIsoOfIsStrictlySupported K e j).inv =
      (K.stupidTruncXIso e h).inv := by
  unfold restrictExtendXIsoOfIsStrictlySupported
  split
  next hj =>
    have hchoose : hj.choose = i :=
      e.injective_f (hj.choose_spec.trans h.symm)
    cases hchoose
    rfl
  next hj => exact (hj ⟨i, h⟩).elim

/-- The supported reconstruction components commute with the differentials. -/
theorem restrictExtendXIsoOfIsStrictlySupported_comm
    [K.IsStrictlySupported e] (i j : J) (_hij : d.Rel i j) :
    (restrictExtendXIsoOfIsStrictlySupported K e i).hom ≫ K.d i j =
      (K.stupidTrunc e).d i j ≫
        (restrictExtendXIsoOfIsStrictlySupported K e j).hom := by
  by_cases hi : ∃ a, e.f a = i
  · by_cases hj : ∃ b, e.f b = j
    · obtain ⟨a, ha⟩ := hi
      obtain ⟨b, hb⟩ := hj
      rw [restrictExtendXIsoOfIsStrictlySupported_hom K e ha,
        restrictExtendXIsoOfIsStrictlySupported_hom K e hb,
        K.stupidTrunc_d_eq e ha hb]
      simp
    · exact (K.isZero_X_of_isStrictlySupported e j (by
        simpa only [not_exists] using hj)).eq_of_tgt _ _
  · exact (K.isZero_stupidTrunc_X e i (by
      simpa only [not_exists] using hi)).eq_of_src _ _

/-- Restriction followed by zero extension reconstructs a homological complex
that is strictly supported on the embedding range. -/
noncomputable def restrictExtendIsoOfIsStrictlySupported
    [K.IsStrictlySupported e] :
    K.stupidTrunc e ≅ K :=
  Hom.isoOfComponents
    (restrictExtendXIsoOfIsStrictlySupported K e)
    (restrictExtendXIsoOfIsStrictlySupported_comm K e)

/-- The forward reconstruction map on every embedding-range component. -/
theorem restrictExtendIsoOfIsStrictlySupported_hom_f
    [K.IsStrictlySupported e] {i : I} {j : J} (h : e.f i = j) :
    (restrictExtendIsoOfIsStrictlySupported K e).hom.f j =
      (K.stupidTruncXIso e h).hom := by
  change (Hom.isoApp (restrictExtendIsoOfIsStrictlySupported K e) j).hom = _
  rw [restrictExtendIsoOfIsStrictlySupported, Hom.isoOfComponents_app,
    restrictExtendXIsoOfIsStrictlySupported_hom K e h]

/-- The inverse reconstruction map on every embedding-range component. -/
theorem restrictExtendIsoOfIsStrictlySupported_inv_f
    [K.IsStrictlySupported e] {i : I} {j : J} (h : e.f i = j) :
    (restrictExtendIsoOfIsStrictlySupported K e).inv.f j =
      (K.stupidTruncXIso e h).inv := by
  change (Hom.isoApp (restrictExtendIsoOfIsStrictlySupported K e) j).inv = _
  rw [restrictExtendIsoOfIsStrictlySupported, Hom.isoOfComponents_app,
    restrictExtendXIsoOfIsStrictlySupported_inv K e h]

/-- Off the embedding range, the forward reconstruction component is the
unique map from the zero source. -/
theorem restrictExtendIsoOfIsStrictlySupported_hom_f_of_notMem
    [K.IsStrictlySupported e] (j : J) (hj : ∀ i, e.f i ≠ j) :
    (restrictExtendIsoOfIsStrictlySupported K e).hom.f j =
      (K.isZero_stupidTrunc_X e j hj).to_ (K.X j) :=
  (K.isZero_stupidTrunc_X e j hj).eq_of_src _ _

/-- Off the embedding range, the inverse reconstruction component is the
unique map from the zero source. -/
theorem restrictExtendIsoOfIsStrictlySupported_inv_f_of_notMem
    [K.IsStrictlySupported e] (j : J) (hj : ∀ i, e.f i ≠ j) :
    (restrictExtendIsoOfIsStrictlySupported K e).inv.f j =
      (K.isZero_X_of_isStrictlySupported e j hj).to_
        ((K.stupidTrunc e).X j) :=
  (K.isZero_X_of_isStrictlySupported e j hj).eq_of_src _ _

/-- The forward supported reconstruction maps are natural in the homological
complex. -/
@[reassoc]
theorem restrictExtendIsoOfIsStrictlySupported_hom_naturality
    {K L : HomologicalComplex C d} [K.IsStrictlySupported e]
    [L.IsStrictlySupported e] (φ : K ⟶ L) :
    stupidTruncMap φ e ≫
        (restrictExtendIsoOfIsStrictlySupported L e).hom =
      (restrictExtendIsoOfIsStrictlySupported K e).hom ≫ φ := by
  ext j
  by_cases hj : ∃ i, e.f i = j
  · obtain ⟨i, hi⟩ := hj
    simpa only [HomologicalComplex.comp_f,
      restrictExtendIsoOfIsStrictlySupported_hom_f K e hi,
      restrictExtendIsoOfIsStrictlySupported_hom_f L e hi] using
      stupidTruncMap_stupidTruncXIso_hom φ e hi
  · exact (K.isZero_stupidTrunc_X e j (by
      simpa only [not_exists] using hj)).eq_of_src _ _

/-- The inverse supported reconstruction maps are natural in the homological
complex. -/
@[reassoc]
theorem restrictExtendIsoOfIsStrictlySupported_inv_naturality
    {K L : HomologicalComplex C d} [K.IsStrictlySupported e]
    [L.IsStrictlySupported e] (φ : K ⟶ L) :
    φ ≫ (restrictExtendIsoOfIsStrictlySupported L e).inv =
      (restrictExtendIsoOfIsStrictlySupported K e).inv ≫
        stupidTruncMap φ e := by
  rw [← cancel_mono (restrictExtendIsoOfIsStrictlySupported L e).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [restrictExtendIsoOfIsStrictlySupported_hom_naturality e φ,
    Iso.inv_hom_id_assoc]

end HomologicalComplex

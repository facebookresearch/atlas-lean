/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.Embedding.StupidTrunc

/-!
# Inclusion of a lower-closed stupid truncation

For an embedding of complex shapes whose image is stable under the next
differential, the stupid truncation is canonically a subcomplex of the
original complex.  This file constructs that inclusion, its component
formulas, monomorphism instances, and naturality.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Category Limits ZeroObject

universe v u

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  (K L : HomologicalComplex C c') (e : c.Embedding c')

variable [e.IsRelIff] in
/-- The differential of a stupid truncation, expressed through its canonical
component isomorphisms on the embedding range. -/
lemma stupidTrunc_d_eq {i j : ι} {i' j' : ι'}
    (hi : e.f i = i') (hj : e.f j = j') :
    (K.stupidTrunc e).d i' j' =
      (K.stupidTruncXIso e hi).hom ≫ K.d i' j' ≫
        (K.stupidTruncXIso e hj).inv := by
  change ((K.restriction e).extend e).d i' j' = _
  rw [(K.restriction e).extend_d_eq e hi hj,
    K.restriction_d_eq e hi hj]
  have hIso_i :
      K.stupidTruncXIso e hi =
        (K.restriction e).extendXIso e hi ≪≫
          K.restrictionXIso e hi := by
    rfl
  have hIso_j :
      K.stupidTruncXIso e hj =
        (K.restriction e).extendXIso e hj ≪≫
          K.restrictionXIso e hj := by
    rfl
  rw [hIso_i, hIso_j]
  simp only [Iso.trans_hom, Iso.trans_inv]
  simp only [← Category.assoc]
  simp only [Category.assoc]
  exact (Category.assoc
    ((K.restriction e).extendXIso e hi).hom
    (K.restrictionXIso e hi).hom
    (K.d i' j' ≫ (K.restrictionXIso e hj).inv ≫
      ((K.restriction e).extendXIso e hj).inv)).symm

namespace stupidTruncι

variable [e.IsRelIff]

open scoped Classical in
/-- Components of the stupid-truncation inclusion. -/
noncomputable def f (i' : ι') : (K.stupidTrunc e).X i' ⟶ K.X i' :=
  if hi' : ∃ i, e.f i = i' then
    (K.stupidTruncXIso e hi'.choose_spec).hom
  else 0

lemma f_eq {i : ι} {i' : ι'} (hi : e.f i = i') :
    f K e i' = (K.stupidTruncXIso e hi).hom := by
  have hi' : ∃ k, e.f k = i' := ⟨i, hi⟩
  have hchoose : hi'.choose = i :=
    e.injective_f (hi'.choose_spec.trans hi.symm)
  simp only [f, dite_eq_left hi']
  subst i
  rfl

lemma f_eq_zero (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    f K e i' = 0 := by
  rw [f, dite_eq_right]
  simpa only [not_exists] using hi'

end stupidTruncι

namespace stupidTruncι

variable [e.IsTruncGE]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma comm (i' j' : ι') :
    f K e i' ≫ K.d i' j' = (K.stupidTrunc e).d i' j' ≫ f K e j' := by
  by_cases hij : c'.Rel i' j'
  · by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi'
      subst i'
      obtain ⟨j, hj⟩ := e.mem_next hij
      rw [f_eq K e rfl, f_eq K e hj, stupidTrunc_d_eq K e rfl hj]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · have hzero := K.isZero_stupidTrunc_X e i' (by simpa using hi')
      exact hzero.eq_of_src _ _
  · rw [K.shape _ _ hij, (K.stupidTrunc e).shape _ _ hij,
      comp_zero, zero_comp]

end stupidTruncι

variable [e.IsTruncGE]

/-- The canonical inclusion of a lower-closed stupid truncation into the
original homological complex. -/
noncomputable def ιStupidTrunc : K.stupidTrunc e ⟶ K where
  f i' := stupidTruncι.f K e i'
  comm' i' j' _ := stupidTruncι.comm K e i' j'

/-- On the embedding range, the inclusion component is the canonical
stupid-truncation component isomorphism. -/
@[simp]
lemma ιStupidTrunc_f {i : ι} {i' : ι'} (hi : e.f i = i') :
    (K.ιStupidTrunc e).f i' = (K.stupidTruncXIso e hi).hom :=
  stupidTruncι.f_eq K e hi

/-- Off the embedding range, the inclusion component is zero. -/
lemma ιStupidTrunc_f_eq_zero (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    (K.ιStupidTrunc e).f i' = 0 :=
  stupidTruncι.f_eq_zero K e i' hi'

instance (i' : ι') : Mono ((K.ιStupidTrunc e).f i') := by
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    rw [ιStupidTrunc_f K e hi]
    infer_instance
  · apply (K.isZero_stupidTrunc_X e i' (by simpa using hi')).mono

instance : Mono (K.ιStupidTrunc e) :=
  HomologicalComplex.mono_of_mono_f _ fun _ => inferInstance

variable {K L}

/-- The stupid-truncation inclusions are natural in the homological complex. -/
@[reassoc (attr := simp)]
theorem stupidTruncMap_ιStupidTrunc_naturality (φ : K ⟶ L) :
    stupidTruncMap φ e ≫ L.ιStupidTrunc e = K.ιStupidTrunc e ≫ φ := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simpa only [HomologicalComplex.comp_f, ιStupidTrunc_f K e hi,
      ιStupidTrunc_f L e hi] using
        stupidTruncMap_stupidTruncXIso_hom φ e hi
  · apply (K.isZero_stupidTrunc_X e i' (by simpa using hi')).eq_of_src

end HomologicalComplex

namespace ComplexShape.Embedding

variable (e : c.Embedding c') [e.IsTruncGE]
  (C : Type u) [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- The canonical inclusion from stupid truncation to the original complex,
as a natural transformation. -/
@[simps]
noncomputable def ιStupidTruncNatTrans :
    e.stupidTruncFunctor C ⟶ 𝟭 (HomologicalComplex C c') where
  app K := K.ιStupidTrunc e
  naturality _ _ f :=
    HomologicalComplex.stupidTruncMap_ιStupidTrunc_naturality e f

end ComplexShape.Embedding

end

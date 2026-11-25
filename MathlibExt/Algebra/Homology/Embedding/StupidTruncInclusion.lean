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
original complex. This file supplements the canonical inclusion with
component formulas and its differential transport law.
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
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]

namespace stupidTruncι

variable [e.IsRelIff]

/-- Components of the canonical stupid-truncation inclusion. -/
noncomputable abbrev f (i' : ι') : (K.stupidTrunc e).X i' ⟶ K.X i' :=
  K.ιStupidTruncf e i'

lemma f_eq {i : ι} {i' : ι'} (hi : e.f i = i') :
    f K e i' = (K.stupidTruncXIso e hi).hom := by
  subst i'
  simp only [f, ιStupidTruncf_eq, stupidTruncXIso_rfl]

lemma f_eq_zero (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    f K e i' = 0 := by
  simp only [f, ιStupidTruncf, dite_eq_right (not_exists.mpr hi')]

end stupidTruncι

namespace stupidTruncι

variable [e.IsTruncGE]

@[reassoc (attr := simp)]
lemma comm (i' j' : ι') :
    f K e i' ≫ K.d i' j' = (K.stupidTrunc e).d i' j' ≫ f K e j' :=
  (K.ιStupidTrunc e).comm i' j'

end stupidTruncι

variable [e.IsTruncGE]

/-- Off the embedding range, the inclusion component is zero. -/
lemma ιStupidTrunc_f_eq_zero (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    (K.ιStupidTrunc e).f i' = 0 :=
  stupidTruncι.f_eq_zero K e i' hi'

variable {K L}

/-- The stupid-truncation inclusions are natural in the homological complex. -/
@[reassoc (attr := simp)]
theorem stupidTruncMap_ιStupidTrunc_naturality (φ : K ⟶ L) :
    stupidTruncMap φ e ≫ L.ιStupidTrunc e = K.ιStupidTrunc e ≫ φ :=
  HomologicalComplex.ιStupidTrunc_naturality φ e

end HomologicalComplex



end

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

public import Mathlib.Algebra.Homology.Embedding.StupidTrunc

/-!
# Inclusion of a lower-closed stupid truncation

For an embedding of complex shapes whose image is stable under the next
differential, the stupid truncation is canonically a subcomplex of the
original complex. Mathlib provides the inclusion, its monomorphism instances,
and its naturality. This file gives formulas for its components and for the
truncation differential.
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
  (K : HomologicalComplex C c') (e : c.Embedding c')

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

variable [e.IsTruncGE]

/-- On the embedding range, the inclusion component is the canonical
stupid-truncation component isomorphism. -/
@[simp]
lemma ιStupidTrunc_f_eq {i : ι} {i' : ι'} (hi : e.f i = i') :
    (K.ιStupidTrunc e).f i' = (K.stupidTruncXIso e hi).hom := by
  subst hi
  rw [ιStupidTrunc_f, ιStupidTruncf_eq, stupidTruncXIso_rfl]

/-- Off the embedding range, the inclusion component is zero. -/
lemma ιStupidTrunc_f_eq_zero (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    (K.ιStupidTrunc e).f i' = 0 :=
  (K.isZero_stupidTrunc_X e i' hi').eq_of_src _ _

end HomologicalComplex

end

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# Naturality of extended chain homotopies

This file records that extension along an embedding of complex shapes preserves
degreewise naturality squares between chain homotopies.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe w w' v u

namespace Homotopy

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C]
variable {I : Type w} {I' : Type w'} {c : ComplexShape I} {c' : ComplexShape I'}
variable {K L K' L' : HomologicalComplex C c}
variable {f g : K ⟶ L} {f' g' : K' ⟶ L'}

/-- Extension along an embedding preserves a degreewise naturality square between homotopies. -/
lemma extend_hom_naturality
    (h : _root_.Homotopy f g) (h' : _root_.Homotopy f' g')
    (a : K ⟶ K') (b : L ⟶ L')
    (hn : ∀ i j, a.f i ≫ h'.hom i j = h.hom i j ≫ b.f j)
    (e : c.Embedding c') [e.IsRelIff] (i' j' : I') :
    (HomologicalComplex.extendMap a e).f i' ≫ (h'.extend e).hom i' j' =
      (h.extend e).hom i' j' ≫ (HomologicalComplex.extendMap b e).f j' := by
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    by_cases hj' : ∃ j, e.f j = j'
    · obtain ⟨j, rfl⟩ := hj'
      rw [HomologicalComplex.extendMap_f _ e rfl,
        HomologicalComplex.extendMap_f _ e rfl,
        _root_.Homotopy.extend_hom_eq _ e rfl rfl,
        _root_.Homotopy.extend_hom_eq _ e rfl rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      simpa only [Category.assoc] using congrArg
        (fun z ↦ (K.extendXIso e rfl).hom ≫ z ≫
          (L'.extendXIso e rfl).inv) (hn i j)
    · exact (L'.isZero_extend_X e j' (by tauto)).eq_of_tgt _ _
  · exact (K.isZero_extend_X e i' (by tauto)).eq_of_src _ _

end Homotopy

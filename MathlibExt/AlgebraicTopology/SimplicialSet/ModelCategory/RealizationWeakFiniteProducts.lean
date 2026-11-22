/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BetaPairTrivialCofibration
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
import MathlibExt.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Finite original products preserve realization weak equivalences

All original simplicial sets are cofibrant. The actual tensor-left Quillen
adjunction and Brown preservation therefore give product weakness without
Kan hypotheses. The whole native product comparison and braiding retain
both original factor maps; finite head/tail induction covers all Fin n,
including the empty original product.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory MonoidalClosed
open scoped MonoidalCategory SSet.modelCategoryQuillen

namespace SSet

/-- The same original product with any raw left factor preserves realization weakness. -/
theorem realizationWeak_prodMap_id_left (K : SSet.{u}) {X Y : SSet.{u}}
    (f : X ⟶ Y) (hf : realizationWeakEquivalences f) :
    realizationWeakEquivalences (prod.map (𝟙 K) f) := by
  let _ : CategoryTheory.Adjunction.IsQuillenAdjunction (ihom.adjunction K) :=
    ihomAdjunction_isQuillenAdjunction_of_isCofibrant K
  let _ : WeakEquivalence f := (weakEquivalence_iff f).mpr hf
  have h : WeakEquivalence ((tensorLeft K).map f) :=
    CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := ihom.adjunction K) f
  exact (realizationWeakEquivalences.arrow_mk_iso_iff (tensorLeftProductArrowIso K f)).mp
    ((weakEquivalence_iff _).mp h)

/-- The same original product with any raw right factor preserves realization weakness. -/
theorem realizationWeak_prodMap_id_right {X Y : SSet.{u}} (f : X ⟶ Y) (K : SSet.{u})
    (hf : realizationWeakEquivalences f) : realizationWeakEquivalences (prod.map f (𝟙 K)) :=
  (realizationWeakEquivalences.arrow_mk_iso_iff (rightProductArrowIso f K)).mp
    (realizationWeak_prodMap_id_left K f hf)

/-- The actual original binary product of any two realization weak maps is weak. -/
theorem realizationWeak_prodMap {X Y A B : SSet.{u}} (f : X ⟶ Y) (g : A ⟶ B)
    (hf : realizationWeakEquivalences f) (hg : realizationWeakEquivalences g) :
    realizationWeakEquivalences (prod.map f g) := by
  have hw := realizationWeakEquivalences.comp_mem _ _
    (realizationWeak_prodMap_id_right f A hf) (realizationWeak_prodMap_id_left Y g hg)
  have he : prod.map f (𝟙 A) ≫ prod.map (𝟙 Y) g = prod.map f g := by
    simpa only [Category.comp_id, Category.id_comp] using prod.map_map f (𝟙 A) (𝟙 Y) g
  exact he ▸ hw

/-- Every original Fin n product of realization weak maps is weak without fibrancy hypotheses. -/
theorem realizationWeak_finPiMap (n : ℕ) {X Y : Fin n → SSet.{u}}
    (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, realizationWeakEquivalences (f i)) :
    realizationWeakEquivalences (CategoryTheory.Limits.Pi.map f) := by
  induction n with
  | zero =>
      let _ : IsIso (CategoryTheory.Limits.Pi.map f) := by
        refine ⟨⟨CategoryTheory.Limits.Pi.lift (fun i => Fin.elim0 i), ?_, ?_⟩⟩
        · apply CategoryTheory.Limits.Pi.hom_ext
          intro i
          exact Fin.elim0 i
        · apply CategoryTheory.Limits.Pi.hom_ext
          intro i
          exact Fin.elim0 i
      exact realizationWeakEquivalences.of_isIso _
  | succ n ih =>
      have htail := ih (fun i : Fin n => f i.succ) (fun i => hf i.succ)
      have hb := realizationWeak_prodMap (f 0)
        (CategoryTheory.Limits.Pi.map (fun i : Fin n => f i.succ)) (hf 0) htail
      exact (realizationWeakEquivalences.arrow_mk_iso_iff
        (CategoryTheory.Limits.Pi.finSuccProductArrowIso n f)).mpr hb

end SSet

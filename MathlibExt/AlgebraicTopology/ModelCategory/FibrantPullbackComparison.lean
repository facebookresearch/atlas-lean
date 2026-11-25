/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.UnderOverProperQuillen
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown

/-!
# Original pullback comparisons between fibrations

A weak map between two fibrations over the same base is a weak map
between fibrant objects of the native Over model category. Pullback is
the existing right Quillen functor, so Brown's lemma proves weakness
of the actual pullback map along any specified base map. No right
properness or identification of homotopy-category pullbacks is needed.
-/

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

private theorem isFibrant_over_of_fibration_hom {B : C} (P : Over B)
    [Fibration P.hom] : IsFibrant P := by
  let t : P ⟶ Over.mk (𝟙 B) := Over.mkIdTerminal.from P
  have ht : Fibration t := (fibrations_over_iff B t).mpr (by
    change Fibration (Over.mkIdTerminal.from P).left
    rw [Over.mkIdTerminal_from_left]
    infer_instance)
  exact (isFibrant_iff_of_isTerminal t Over.mkIdTerminal).mpr ht

/-- Pullback along any specified map preserves an original weak comparison
between two fibrations over the identical base, with both original pullback legs. -/
theorem weakEquivalence_pullback_map_of_fibrations {B X Y A : C}
    (p : X ⟶ B) (q : Y ⟶ B) (f : X ⟶ Y) (hf : f ≫ q = p)
    [Fibration p] [Fibration q] [WeakEquivalence f] (a : A ⟶ B) :
    WeakEquivalence (pullback.map p a q a f (𝟙 A) (𝟙 B)
      ((Category.comp_id p).trans hf.symm) (by simp)) := by
  let P : Over B := Over.mk p
  let Q : Over B := Over.mk q
  let t : P ⟶ Q := Over.homMk f hf
  let _ : Fibration P.hom := by
    change Fibration p
    infer_instance
  let _ : Fibration Q.hom := by
    change Fibration q
    infer_instance
  let _ : IsFibrant P := isFibrant_over_of_fibration_hom P
  let _ : IsFibrant Q := isFibrant_over_of_fibration_hom Q
  let _ : WeakEquivalence t := (weakEquivalences_over_iff B t).mpr
    (inferInstanceAs (WeakEquivalence f))
  let _ : (Over.mapPullbackAdj a).IsQuillenAdjunction :=
    Over.mapPullbackAdj_isQuillenAdjunction a
  have hw : WeakEquivalence ((Over.pullback a).map t) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
      (adj := Over.mapPullbackAdj a) t
  have hraw : WeakEquivalence ((Over.pullback a).map t).left :=
    (weakEquivalences_over_iff A _).mp hw
  have heq : ((Over.pullback a).map t).left =
      pullback.map p a q a f (𝟙 A) (𝟙 B)
        ((Category.comp_id p).trans hf.symm) (by simp) := by
    change pullback.lift (pullback.fst p a ≫ f) (pullback.snd p a) _ = _
    simp only [pullback.map, Category.comp_id]
    rfl
  exact heq ▸ hraw

/-- The same weak comparison for any two actual pullback squares, retaining
their supplied projections and the specified whole comparison map. -/
theorem weakEquivalence_of_isPullback_pair {B X Y A S T : C}
    (p : X ⟶ B) (q : Y ⟶ B) (f : X ⟶ Y) (hf : f ≫ q = p)
    [Fibration p] [Fibration q] [WeakEquivalence f] (a : A ⟶ B)
    (sf : S ⟶ X) (sa : S ⟶ A) (tf : T ⟶ Y) (ta : T ⟶ A)
    (hS : IsPullback sf sa p a) (hT : IsPullback tf ta q a)
    (k : S ⟶ T) (hkf : k ≫ tf = sf ≫ f) (hka : k ≫ ta = sa) :
    WeakEquivalence k := by
  let d := pullback.map p a q a f (𝟙 A) (𝟙 B)
    ((Category.comp_id p).trans hf.symm) (by simp)
  have hd : WeakEquivalence d :=
    weakEquivalence_pullback_map_of_fibrations p q f hf a
  have hcomm : hS.isoPullback.hom ≫ d = k ≫ hT.isoPullback.hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc, d, pullback.map, pullback.lift_fst,
        hS.isoPullback_hom_fst_assoc, hT.isoPullback_hom_fst]
      exact hkf.symm
    · simp only [Category.assoc, d, pullback.map, pullback.lift_snd,
        Category.comp_id, hS.isoPullback_hom_snd, hT.isoPullback_hom_snd]
      exact hka.symm
  exact (weakEquivalence_iff k).mpr
    (((weakEquivalences C).arrow_mk_iso_iff
      (Arrow.isoMk hS.isoPullback hT.isoPullback hcomm)).mpr
        ((weakEquivalence_iff d).mp hd))

end HomotopicalAlgebra

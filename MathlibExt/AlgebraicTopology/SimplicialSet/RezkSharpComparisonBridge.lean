/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SharpRecognition
import MathlibExt.AlgebraicTopology.SimplicialSet.RezkDiagonalSharpHomotopyPullback

/-!
# The SAME original sharpness class and actual Rezk diagonal theorem

The native universal base-change class and the original full native
homotopy-pullback comparison class agree on every original simplicial
map. Both all-simplex criteria retain the same pullbacks, projections
and ordinal maps. The proved original Rezk diagonal theorem is reused
with its full original row and relative-operator hypotheses.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

/-- Every SAME native simplex transition is the original comparison
map after its actual costructured-arrow triangle. -/
lemma simplexPullbackTransition_eq_originalComparison {E B : SSet.{u}} (p : E ⟶ B)
    {s t : SimplexIndex B} (a : s ⟶ t) :
    (simplexPullbackDiagram p).map a =
      pullback.map p s.hom p t.hom (𝟙 E) (SSet.stdSimplex.map a.left) (𝟙 B)
        (by simp) (by simpa only [Category.comp_id] using (CostructuredArrow.w a).symm) := by
  apply pullback.hom_ext <;> simp [simplexPullbackDiagram, simplexPullbackMap, pullback.map]

/-- The two complete original all-simplex conditions are equivalent. -/
theorem allSimplexComparisons_iff_nativeTransitions {E B : SSet.{u}} (p : E ⟶ B) :
    SharpSaturation.allSimplexComparisons p ↔
      ∀ {s t : SimplexIndex B} (a : s ⟶ t),
        realizationWeakEquivalences ((simplexPullbackDiagram p).map a) := by
  constructor
  · intro h s t a
    have hw := h t.left.len s.left.len t.hom a.left
    let e : Arrow.mk ((simplexPullbackDiagram p).map a) ≅
        Arrow.mk (pullback.map p (SSet.stdSimplex.map a.left ≫ t.hom) p t.hom
          (𝟙 E) (SSet.stdSimplex.map a.left) (𝟙 B) (by simp) (by simp)) :=
      Arrow.isoMk (pullback.congrHom rfl (CostructuredArrow.w a).symm) (Iso.refl _) (by
        apply pullback.hom_ext <;>
          simp [simplexPullbackDiagram, simplexPullbackMap, pullback.map, pullback.congrHom])
    exact (realizationWeakEquivalences.arrow_mk_iso_iff e).mpr hw
  · intro h n m b f
    let s : SimplexIndex B := CostructuredArrow.mk (SSet.stdSimplex.map f ≫ b)
    let t : SimplexIndex B := CostructuredArrow.mk b
    let a : s ⟶ t := CostructuredArrow.homMk f rfl
    have hh := h a
    rw [simplexPullbackTransition_eq_originalComparison] at hh
    exact hh

/-- The SAME original universal and native-homotopy-comparison sharpness predicates agree. -/
theorem sharpMaps_iff_originalComparisonSharp {E B : SSet.{u}} (p : E ⟶ B) :
    MorphismProperty.sharpMaps realizationWeakEquivalences p ↔ SharpComparisonDraft.Sharp p :=
  (sharpMaps_iff_simplexPullbackTransitions p).trans
    ((allSimplexComparisons_iff_nativeTransitions p).symm.trans
      (SharpSaturation.sharp_iff_allSimplexComparisons p).symm)

/-- The full original Rezk6.1 theorem applies to the SAME native sharp
row maps and EVERY actual original relative-operator comparison. -/
theorem rezk_diagonal_sharp_and_original_kappa
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (hrows : ∀ n : SimplexCategory, MorphismProperty.sharpMaps realizationWeakEquivalences (η.app (op n)))
    (hoperators : ∀ {n m : SimplexCategory} (f : n ⟶ m),
      WeakEquivalence (EquifibredDiagonal.relativeComparison η f)) :
    MorphismProperty.sharpMaps realizationWeakEquivalences (simplicialDiagonalFunctor.map η) ∧
      ∀ (n : SimplexCategory) (v : Fin (n.len + 1)), WeakEquivalence (RezkOriginal61.kappa η n v) := by
  have h := RezkOriginal61.all_simplex_sharp_and_native_homotopy_pullback η
    (fun n => (sharpMaps_iff_originalComparisonSharp _).mp (hrows n)) hoperators
  exact ⟨(sharpMaps_iff_originalComparisonSharp _).mpr h.2.1, h.2.2⟩

end SSet

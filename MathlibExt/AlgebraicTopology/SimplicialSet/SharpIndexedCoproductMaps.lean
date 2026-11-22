/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SSetCoproducts
import MathlibExt.AlgebraicTopology.SimplicialSet.RezkSharpComparisonBridge
import MathlibExt.CategoryTheory.Limits.Shapes.Pullback.BaseChangeSquareIso

/-!
# Sharpness of the SAME original full indexed coproduct map

Every represented simplex of the original coproduct base lies in one
actual component. Native disjointness gives its full original pullback
square. Both complete comparison maps are carried through the original
pasted pullback isomorphisms, preserving every ordinal and projection.
-/

noncomputable section
universe u
open CategoryTheory Limits
open scoped Simplicial

namespace SSet

/-- Every SAME entire original coproduct map is sharp when each whole
original component map is sharp, including arbitrary and empty indices. -/
theorem sharpMaps_sigmaMap {I : Type u} {X Y : I → SSet.{u}} (p : ∀ i, X i ⟶ Y i)
    (hp : ∀ i, MorphismProperty.sharpMaps realizationWeakEquivalences (p i)) :
    MorphismProperty.sharpMaps realizationWeakEquivalences (Limits.Sigma.map p) := by
  apply (sharpMaps_iff_originalComparisonSharp _).mpr
  apply (SharpSaturation.sharp_iff_allSimplexComparisons _).mpr
  intro n m b f
  obtain ⟨i, β, hb⟩ := exists_sigma_ι_comp_eq b
  let H := isPullback_sigma_ι_sigmaMap p i
  let eS := IsPullback.baseChangeSquareIso H (SSet.stdSimplex.map f ≫ β)
    (SSet.stdSimplex.map f ≫ b) (by rw [Category.assoc, hb])
  let eT := IsPullback.baseChangeSquareIso H β b hb
  have h := (SharpSaturation.sharp_iff_allSimplexComparisons (p i)).mp
    ((sharpMaps_iff_originalComparisonSharp _).mp (hp i)) n m β f
  let a : Arrow.mk (pullback.map (p i) (SSet.stdSimplex.map f ≫ β) (p i) β
      (𝟙 (X i)) (SSet.stdSimplex.map f) (𝟙 (Y i)) (by simp) (by simp)) ≅
      Arrow.mk (pullback.map (Limits.Sigma.map p) (SSet.stdSimplex.map f ≫ b) (Limits.Sigma.map p) b
        (𝟙 (∐ X)) (SSet.stdSimplex.map f) (𝟙 (∐ Y)) (by simp) (by simp)) :=
    Arrow.isoMk' _ _ eS eT (IsPullback.baseChangeSquareIso_natural H β b hb (SSet.stdSimplex.map f))
  exact (realizationWeakEquivalences.arrow_mk_iso_iff a).mp h

end SSet

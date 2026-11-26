/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFullBoundaryNegativeMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornShortLegs

/-!
# Same complete positive boundary Hom maps

The full boundary contains both endpoint faces. Every inner-horn
Restriction therefore extracts the same short Hom maps and
the same complete positive composition-face map. All 
vertices, scalar maps and endpoint equations are retained.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.BoundaryHomFaces
open SimplicialEnrichment HornBoxFaces

variable {C : Carrier.{u}} {n : ℕ}
  (f : (∂Δ[n + 2] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)

/-- The canonical interior index, available in every dimension at least two. -/
def canonicalIndex : Fin (n + 3) := 1

/-- The canonical index is strictly after the first endpoint. -/
theorem canonicalIndex_ne_zero : canonicalIndex (n := n) ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  change 1 = 0 at hv
  omega

/-- The canonical index is strictly before the last endpoint. -/
theorem canonicalIndex_ne_last : canonicalIndex (n := n) ≠ Fin.last (n + 2) := by
  intro h
  have hv := congrArg Fin.val h
  change 1 = n + 2 at hv
  omega

/-- The left short Hom is extracted from the same full boundary endpoint faces. -/
def leftMap (b : Interior.{u} n) :
    nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3))) b.val) ⟶
      (BoundaryFaces.object f 0 ⟶[SSet.{u}] BoundaryFaces.object f (HornBoxFaces.vertex b)) :=
  HornBoxFaces.leftMap (BoundaryFaces.horn f canonicalIndex)
    canonicalIndex_ne_zero canonicalIndex_ne_last b

/-- The right short Hom is extracted from the same full boundary endpoint faces. -/
def rightMap (b : Interior.{u} n) :
    nerve (SimplicialThickening.Path b.val (ULift.up.{u} (Fin.last (n + 2)))) ⟶
      (BoundaryFaces.object f (HornBoxFaces.vertex b) ⟶[SSet.{u}] BoundaryFaces.object f
        (Fin.last (n + 2))) :=
  HornBoxFaces.rightMap (BoundaryFaces.horn f canonicalIndex)
    canonicalIndex_ne_zero canonicalIndex_ne_last b

/-- Every retaining inner horn reads the same left boundary Hom map. -/
theorem leftMap_horn (i : Fin (n + 3)) (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2))
    (b : Interior.{u} n) :
    HornBoxFaces.leftMap (BoundaryFaces.horn f i) hi₀ hiₙ b = leftMap f b := by
  rw [HornShortLegs.leftMap_eq_lastFace]
  unfold leftMap
  rw [HornShortLegs.leftMap_eq_lastFace]
  rfl

/-- Every retaining inner horn reads the same right boundary Hom map. -/
theorem rightMap_horn (i : Fin (n + 3)) (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2))
    (b : Interior.{u} n) :
    HornBoxFaces.rightMap (BoundaryFaces.horn f i) hi₀ hiₙ b = rightMap f b := by
  rw [HornShortLegs.rightMap_eq_firstFace]
  unfold rightMap
  rw [HornShortLegs.rightMap_eq_firstFace]
  rfl

/-- The complete positive composition-face map uses both same short Hom maps. -/
def positiveMap (b : Interior.{u} n) :
    (CompositionFace.positive (ULift.up 0) b.val (ULift.up (Fin.last (n + 2))) : SSet.{u}) ⟶
      (BoundaryFaces.object f 0 ⟶[SSet.{u}] BoundaryFaces.object f (Fin.last (n + 2))) :=
  (CompositionFace.positiveIso (ULift.up 0) b.val (ULift.up (Fin.last (n + 2)))).inv ≫
    (leftMap f b ⊗ₘ rightMap f b) ≫
      eComp SSet.{u} (BoundaryFaces.object f 0) (BoundaryFaces.object f (HornBoxFaces.vertex b))
        (BoundaryFaces.object f (Fin.last (n + 2)))

/-- Every inner-horn restriction extracts the same positive
boundary map. -/
theorem positiveMap_horn (i : Fin (n + 3)) (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2))
    (b : Interior.{u} n) :
    HornBoxFaces.positiveMap (BoundaryFaces.horn f i) hi₀ hiₙ b = positiveMap f b := by
  unfold HornBoxFaces.positiveMap positiveMap
  rw [leftMap_horn, rightMap_horn]
  rfl

end CategoryTheory.CoherentRealization.BoundaryHomFaces

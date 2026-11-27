/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornOutsideIntervals

/-!
# Original preimage equality for an actual whole outside-face map

Equality of the two original source vertices gives the same whole face
map at fixed original target endpoints. All supplied interval and endpoint
equations are retained, including their dependent source types.
-/

noncomputable section
universe u
open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OutsideFaceMapCongruence
open SimplicialEnrichment

/-- Replacing original outside-face preimages by equal vertices preserves the entire Hom map
at the same
  supplied original target endpoints. -/
theorem source_eq {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
    (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
    (j : Fin (n + 3)) (hj : j ≠ i) (a' b' c' d' : ULift.{u} (Fin (n + 2)))
    (hA : a' = c') (hB : b' = d')
    (h₁ : (ULift.up j : ULift.{u} (Fin (n + 3))) < (OrdinalFace.embedding j) a' ∨
      (OrdinalFace.embedding j)
      b' < ULift.up j)
    (h₂ : (ULift.up j : ULift.{u} (Fin (n + 3))) < (OrdinalFace.embedding j) c' ∨
      (OrdinalFace.embedding j)
      d' < ULift.up j)
    {a b : Fin (n + 3)} (ha₁ : j.succAbove a'.down = a) (hb₁ : j.succAbove b'.down = b)
    (ha₂ : j.succAbove c'.down = a) (hb₂ : j.succAbove d'.down = b) :
    HornOutsideIntervals.faceMap f j hj a' b' h₁ ha₁ hb₁ =
      HornOutsideIntervals.faceMap f j hj c' d' h₂ ha₂ hb₂ := by
  subst c'
  subst d'
  rfl

end CategoryTheory.CoherentRealization.OutsideFaceMapCongruence

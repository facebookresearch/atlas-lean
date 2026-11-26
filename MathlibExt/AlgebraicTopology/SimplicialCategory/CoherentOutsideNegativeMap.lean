/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentNegativeFaceOverlap
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornOutsideIntervals

/-!
# Actual outside-face Hom maps restrict to their original negative maps

The whole Hom map extracted from a supplied outside ordinal face restricts
along its actual negative-subcomplex inclusion to the original supplied
negative-face map. The proof uses both genuine Hom comparisons and their
whole original face-operator equations. No higher or Kan hypothesis is
needed.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OutsideNegativeMap
open SimplicialEnrichment HornHomFaces
variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (j : Fin (n + 3)) (hj : j ≠ i) (a b : ULift.{u} (Fin (n + 2)))
  (hout : (ULift.up j : ULift.{u} (Fin (n + 3))) < (OrdinalFace.embedding j) a ∨
    (OrdinalFace.embedding j) b < ULift.up j)

/-- The actual whole outside-face Hom map restricts to the supplied original negative face, with both exact
  endpoints. -/
theorem restriction :
    (HomBoxDecomposition.negative ((OrdinalFace.embedding j) a) (ULift.up j) ((OrdinalFace.embedding j) b)).ι ≫
      HornOutsideIntervals.faceMap f j hj a b hout rfl rfl = negativeMap f j hj a b := by
  let E := OrdinalFace.negativeIso j a b
  let G := HornOutsideIntervals.faceMap f j hj a b hout rfl rfl
  apply (cancel_epi E.hom).mp
  have h₁ := (Category.assoc E.hom
    (HomBoxDecomposition.negative ((OrdinalFace.embedding j) a) (ULift.up j) ((OrdinalFace.embedding j) b)).ι G).symm
  have h₂ := congrArg (fun h => h ≫ G) (OrdinalFace.negativeIso_operator j a b)
  have h₃ := congrArg (fun h => h ≫ G) (IntervalFaceCover.outsideIso_operator j a b hout).symm
  have h₄ := HornOutsideIntervals.faceMap_readback f j hj a b hout rfl rfl
  have hR := negativeMap_readback f j hj a b
  have hL : E.hom ≫
      ((HomBoxDecomposition.negative ((OrdinalFace.embedding j) a) (ULift.up j) ((OrdinalFace.embedding j) b)).ι ≫ G) =
      HornHomFaces.faceMap f j hj (.mk a) (.mk b) :=
    h₁.trans (h₂.trans (h₃.trans h₄))
  exact hL.trans hR.symm

end CategoryTheory.CoherentRealization.OutsideNegativeMap

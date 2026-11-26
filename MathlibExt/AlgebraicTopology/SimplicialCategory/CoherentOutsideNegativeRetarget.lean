/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentOutsideNegativeMap

/-!
# Actual endpoint-retargeted outside maps on their negative faces

The whole outside-face extraction and the supplied negative-face map
agree under the same two original endpoint equalities. Both the original
Hom-source transport and the individual target-object transport are
retained. No Kan or coherence conclusion is an input.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OutsideNegativeRetarget
open SimplicialEnrichment HornHomFaces
variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (j : Fin (n + 3)) (hj : j ≠ i) (a b : ULift.{u} (Fin (n + 2)))
  (hout : (ULift.up j : ULift.{u} (Fin (n + 3))) < (OrdinalFace.embedding j) a ∨
    (OrdinalFace.embedding j) b < ULift.up j)
  {x y : Fin (n + 3)} (hx : j.succAbove a.down = x) (hy : j.succAbove b.down = y)

/-- Whole outside and negative-face maps retain the same two exact original endpoint transports. -/
theorem restriction :
    (HomBoxDecomposition.negative ((OrdinalFace.embedding j) a) (ULift.up j) ((OrdinalFace.embedding j) b)).ι ≫
      eqToHom (congrArg₂ (fun x y : Fin (n + 3) => nerve (SimplicialThickening.Path (ULift.up.{u} x)
        (ULift.up.{u} y))) hx hy) ≫
        HornOutsideIntervals.faceMap f j hj a b hout hx hy =
      negativeMap f j hj a b ≫ eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y)
        (congrArg (HornFaces.object f) hx) (congrArg (HornFaces.object f) hy)) := by
  let E := OrdinalFace.negativeIso j a b
  let G := HornOutsideIntervals.faceMap f j hj a b hout hx hy
  let S := eqToHom (congrArg₂ (fun x y : Fin (n + 3) =>
    nerve (SimplicialThickening.Path (ULift.up.{u} x) (ULift.up.{u} y))) hx hy)
  let T := eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y)
    (congrArg (HornFaces.object f) hx) (congrArg (HornFaces.object f) hy))
  apply (cancel_epi E.hom).mp
  have h₁ := (Category.assoc E.hom
    (HomBoxDecomposition.negative ((OrdinalFace.embedding j) a) (ULift.up j) ((OrdinalFace.embedding j)
      b)).ι (S ≫ G)).symm
  have h₂ := congrArg (fun h => h ≫ (S ≫ G)) (OrdinalFace.negativeIso_operator j a b)
  have h₃ := congrArg (fun h => h ≫ (S ≫ G)) (IntervalFaceCover.outsideIso_operator j a b hout).symm
  have h₄ := HornOutsideIntervals.faceMap_readback f j hj a b hout hx hy
  have hL := h₁.trans (h₂.trans (h₃.trans h₄))
  have hR := (Category.assoc E.hom (negativeMap f j hj a b) T).symm.trans
    (congrArg (fun h => h ≫ T) (negativeMap_readback f j hj a b))
  exact hL.trans hR.symm

end CategoryTheory.CoherentRealization.OutsideNegativeRetarget

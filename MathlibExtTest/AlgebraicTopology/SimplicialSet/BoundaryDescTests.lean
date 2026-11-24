/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryMatchingLift

/-!
# Standard-boundary descent consumer tests

Checks the empty-intersection two-vertex case and the general compatible-face
computation used by Kan recognition and minimal-fibration rigidity.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.BoundaryDescTests

variable {X : SSet.{u}}

example (n : ℕ) :
    SSet.boundary.IsCompatible
      (fun r : Fin (n + 2) ↦ SSet.boundary.ι r) :=
  SSet.boundary.ι_isCompatible n

example (n : ℕ) :
    IsColimit
      ((SSet.boundary.multicoequalizerDiagram.{u} n).multicofork.toLinearOrder.map
        SSet.Subcomplex.toSSetFunctor) :=
  SSet.boundary.isColimit n

/-- The map glued from the two unconstrained faces of the one-simplex boundary. -/
noncomputable def boundaryOneDesc
    (faces : Fin 2 → ((Δ[0] : SSet.{u}) ⟶ X)) :
    (SSet.boundary 1 : SSet.{u}) ⟶ X :=
  (show SSet.boundary.IsCompatible faces from trivial).desc

example (faces : Fin 2 → ((Δ[0] : SSet.{u}) ⟶ X)) (j : Fin 2) :
    SSet.boundary.ι j ≫ boundaryOneDesc faces = faces j := by
  simp [boundaryOneDesc]

variable {n : ℕ}
  (faces : Fin (n + 3) → ((Δ[n + 1] : SSet.{u}) ⟶ X))
  (hfaces : ∀ (j k : Fin (n + 3)) (hjk : j < k),
    SSet.stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ faces j =
      SSet.stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ faces k)

/-- The map glued from a compatible family of positive-dimensional boundary faces. -/
noncomputable def boundarySuccDesc :
    (SSet.boundary (n + 2) : SSet.{u}) ⟶ X :=
  ((SSet.boundary.isCompatible_succ_iff faces).2 hfaces).desc

example (j : Fin (n + 3)) :
    SSet.boundary.ι j ≫ boundarySuccDesc faces hfaces = faces j := by
  simp [boundarySuccDesc]

/-- The two faces, as maps rather than just vertices, are retained in order. -/
example : (coprod.inl : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]) ≫
    SSet.boundaryOneIsoTwoPoints.inv = SSet.boundary.ι (0 : Fin 2) :=
  SSet.boundaryOneIsoTwoPoints_inl_inv

example : (coprod.inr : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]) ≫
    SSet.boundaryOneIsoTwoPoints.inv = SSet.boundary.ι (1 : Fin 2) :=
  SSet.boundaryOneIsoTwoPoints_inr_inv

example (x : X _⦋0⦌) :
    (SSet.BoundaryMatching.matchingBoundaryIso X 0).hom
        (SimplicialObject.matchingMap X 0 x) =
      (SSet.boundary 0).ι ≫ SSet.yonedaEquiv.symm x :=
  SSet.BoundaryMatching.matchingMap_readback X 0 x

example {Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    HasLiftingProperty (SSet.boundary n).ι f ↔
      Function.Surjective (SimplicialObject.relativeMatchingMap f n) :=
  (SSet.BoundaryMatching.relativeMatching_surjective_iff_hasLiftingProperty_boundary f n).symm

#print axioms SSet.boundary.IsCompatible.desc
#print axioms SSet.boundary.IsCompatible.ι_desc

end MathlibExtTest.AlgebraicTopology.SimplicialSet.BoundaryDescTests

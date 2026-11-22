/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCoordinateColimit

/-!
# Original full marked root-coordinate faces and all pair intersections

The complete original coordinate-face indexing and both membership
labels are retained. Each full pair intersection inherits the same
original root maximum marking and unchanged coordinate projections.
The original subcomplex equality swaps the same two full coordinates
without changing the underlying original scalar words or marks.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- All actual original positive root coordinates retain both original lower and upper membership labels. -/
abbrev RootCoordinateIndex (n : ℕ) := ConeCoordinateFaceIndex (⊥ : Vertex.{u} (n + 1))

/-- The unchanged original lower coordinate label at the root. -/
def coneRootLowerIndex (n : ℕ) (j : Fin (n + 2)) (hj : 0 < j) : RootCoordinateIndex.{u} n :=
  (⟨ULift.up j, hj⟩, false)

/-- The unchanged original upper coordinate label at the root. -/
def coneRootUpperIndex (n : ℕ) (j : Fin (n + 2)) (hj : 0 < j) : RootCoordinateIndex.{u} n :=
  (⟨ULift.up j, hj⟩, true)

/-- Each actual original whole root-coordinate face retains its same inherited original maximum mark. -/
def coneRootCoordinateFaceWeight (n : ℕ) (a : RootCoordinateIndex.{u} n) : Marked.{u} :=
  comap (coneWeight (⊥ : Vertex.{u} (n + 1))) (coneCoordinateFaceAt (⊥ : Vertex.{u} (n + 1)) a).ι

/-- The unchanged original full marked coordinate-face inclusion in the original root cone. -/
def coneRootCoordinateFaceInclusion (n : ℕ) (a : RootCoordinateIndex.{u} n) :
    coneRootCoordinateFaceWeight n a ⟶ coneWeight (⊥ : Vertex.{u} (n + 1)) :=
  comapHom (coneWeight (⊥ : Vertex.{u} (n + 1))) (coneCoordinateFaceAt (⊥ : Vertex.{u} (n + 1)) a).ι

/-- Every original full ordered coordinate intersection retains both original face labels and every inherited
original maximum mark. -/
def coneRootCoordinatePairWeight (n : ℕ) (a b : RootCoordinateIndex.{u} n) : Marked.{u} :=
  comap (coneWeight (⊥ : Vertex.{u} (n + 1)))
    (coneCoordinateFaceAt (⊥ : Vertex.{u} (n + 1)) a ⊓ coneCoordinateFaceAt (⊥ : Vertex.{u} (n + 1)) b).ι

/-- The unchanged original full marked pair-intersection inclusion in the original root cone. -/
def coneRootCoordinatePairInclusion (n : ℕ) (a b : RootCoordinateIndex.{u} n) :
    coneRootCoordinatePairWeight n a b ⟶ coneWeight (⊥ : Vertex.{u} (n + 1)) :=
  comapHom (coneWeight (⊥ : Vertex.{u} (n + 1)))
    (coneCoordinateFaceAt (⊥ : Vertex.{u} (n + 1)) a ⊓ coneCoordinateFaceAt (⊥ : Vertex.{u} (n + 1)) b).ι

/-- The original first coordinate projection of every actual whole marked pair intersection. -/
def coneRootCoordinatePairLeft (n : ℕ) (a b : RootCoordinateIndex.{u} n) :
    coneRootCoordinatePairWeight n a b ⟶ coneRootCoordinateFaceWeight n a :=
  (subcomplexFunctor (coneWeight (⊥ : Vertex.{u} (n + 1)))).map (homOfLE inf_le_left)

/-- The original second coordinate projection of every actual whole marked pair intersection. -/
def coneRootCoordinatePairRight (n : ℕ) (a b : RootCoordinateIndex.{u} n) :
    coneRootCoordinatePairWeight n a b ⟶ coneRootCoordinateFaceWeight n b :=
  (subcomplexFunctor (coneWeight (⊥ : Vertex.{u} (n + 1)))).map (homOfLE inf_le_right)

/-- Every original first coordinate projection retains the same whole original pair inclusion. -/
theorem coneRootCoordinatePairLeft_inclusion (n : ℕ) (a b : RootCoordinateIndex.{u} n) :
    coneRootCoordinatePairLeft n a b ≫ coneRootCoordinateFaceInclusion n a = coneRootCoordinatePairInclusion n a b := by
  apply Hom.ext
  rfl

/-- Every original second coordinate projection retains the same whole original pair inclusion. -/
theorem coneRootCoordinatePairRight_inclusion (n : ℕ) (a b : RootCoordinateIndex.{u} n) :
    coneRootCoordinatePairRight n a b ≫ coneRootCoordinateFaceInclusion n b = coneRootCoordinatePairInclusion n a b
      := by
  apply Hom.ext
  rfl

/-- The original subcomplex intersection symmetry gives the genuine full marked coordinate-swap isomorphism with all
original simplex words and markings retained. -/
def coneRootCoordinatePairSwapIso (n : ℕ) (a b : RootCoordinateIndex.{u} n) :
    coneRootCoordinatePairWeight n a b ≅ coneRootCoordinatePairWeight n b a :=
  (subcomplexFunctor (coneWeight (⊥ : Vertex.{u} (n + 1)))).mapIso
    (eqToIso (inf_comm (coneCoordinateFaceAt (⊥ : Vertex.{u} (n + 1)) a)
      (coneCoordinateFaceAt (⊥ : Vertex.{u} (n + 1)) b)))

/-- The actual full marked coordinate swap retains precisely the original second projection as its new first
projection. -/
theorem coneRootCoordinatePairSwapIso_left (n : ℕ) (a b : RootCoordinateIndex.{u} n) :
    (coneRootCoordinatePairSwapIso n a b).hom ≫ coneRootCoordinatePairLeft n b a = coneRootCoordinatePairRight n a b
      := by
  apply Hom.ext
  rfl

/-- The actual full marked coordinate swap retains precisely the original first projection as its new second
projection. -/
theorem coneRootCoordinatePairSwapIso_right (n : ℕ) (a b : RootCoordinateIndex.{u} n) :
    (coneRootCoordinatePairSwapIso n a b).hom ≫ coneRootCoordinatePairRight n b a = coneRootCoordinatePairLeft n a b
      := by
  apply Hom.ext
  rfl

end SSet.Marked.CoherentWeight

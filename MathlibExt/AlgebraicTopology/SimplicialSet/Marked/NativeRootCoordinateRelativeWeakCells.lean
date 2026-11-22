/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinateScalarControlled
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinateRelativeVertices

/-!
# Genuine weak cells on the unchanged original relative root-cube index

The same original relative nondegenerate scalar determines its complete
first and last subsets, both maxima and its actual positive dimension.
Thus every nonterminal positive original coordinate gives the genuine
weak marked scalar cell without endpoint or weak-class certificates as
inputs. Arbitrary original maximal scalar tensors retain that same whole
coefficient cell and its original marked maps.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq coefficientMarkedModelCategory

/-- A positive nonterminal original coface has a positive-dimensional original smaller root cube. -/
theorem nativeRootCoordinate_inner_positive_dimension {n : ℕ} (j : Fin (n + 2))
    (hj : 0 < j) (hj' : j < Fin.last (n + 1)) : 0 < n := by
  change 0 < j.val at hj
  change j.val < n + 1 at hj'
  omega

/-- The same whole original relative scalar cell is genuinely a coefficient trivial cofibration, with all endpoint
and dimension conditions proved from its original native index. -/
theorem nativeRootCoordinateRelativeCell_coefficientTrivialCofibration {n : ℕ}
    (j : Fin (n + 2)) (hj : 0 < j) (hj' : j < Fin.last (n + 1))
    (s : (coneCoordinateBoundary (⊥ : Vertex.{u} n)).N) :
    trivialCofibrations Marked.{u} (coneRootCoordinateScalarCell j hj s.simplex) := by
  obtain ⟨h₀, h₁⟩ := coneRootCoordinateRelative_native_maxima s
  have hd := coneRootCoordinateRelative_native_positive_dim
    (nativeRootCoordinate_inner_positive_dimension j hj hj') s
  exact coneRootCoordinateScalarCell_trivialCofibration j hj hj' hd s.simplex h₀ h₁

/-- Every actual original ambient mark already belongs to the literal endpoint/scalar-boundary source of this same
original relative root-cube cell. -/
theorem nativeRootCoordinateRelativeCell_marks_mem {n : ℕ}
    (j : Fin (n + 2)) (hj : 0 < j) (hj' : j < Fin.last (n + 1))
    (s : (coneCoordinateBoundary (⊥ : Vertex.{u} n)).N)
    (e : ((Δ[1] : SSet.{u}) ⊗ Δ[s.dim]) _⦋1⦌)
    (he : e ∈ (coneRootCoordinateScalarAmbient j hj s.simplex).marking) :
    e ∈ (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} s.dim)).obj (op ⦋1⦌) := by
  obtain ⟨h₀, h₁⟩ := coneRootCoordinateRelative_native_maxima s
  have hd := coneRootCoordinateRelative_native_positive_dim
    (nativeRootCoordinate_inner_positive_dimension j hj hj') s
  exact coneRootCoordinateScalarAmbient_marks_mem j hj hj' hd s.simplex h₀ h₁ e he

/-- The actual relative marked root-coordinate cell retains precisely its unchanged whole original
endpoint/scalar-boundary simplicial inclusion. -/
theorem nativeRootCoordinateRelativeCell_hom {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (s : (coneCoordinateBoundary (⊥ : Vertex.{u} n)).N) :
    (coneRootCoordinateScalarCell j hj s.simplex).hom =
      (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} s.dim)).ι := rfl

/-- Every unchanged original relative coordinate cell remains a genuine coefficient trivial cofibration after
tensoring with an arbitrary original maximal scalar, including non-Kan scalars. -/
theorem nativeRootCoordinateRelativeCell_maxTensor_trivialCofibration {n : ℕ}
    (j : Fin (n + 2)) (hj : 0 < j) (hj' : j < Fin.last (n + 1))
    (s : (coneCoordinateBoundary (⊥ : Vertex.{u} n)).N) (K : SSet.{u}) :
    trivialCofibrations Marked.{u}
      (prodMap (𝟙 (max K)) (coneRootCoordinateScalarCell j hj s.simplex)) :=
  coefficientMaxTensor_preserves_trivialCofibrations _
    (nativeRootCoordinateRelativeCell_coefficientTrivialCofibration j hj hj' s) K

end SSet.Marked.CoherentWeight

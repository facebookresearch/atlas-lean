/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Empty realized boundary of the zero-simplex

The simplicial boundary ∂Δ[0] is the empty subcomplex. Geometric realization preserves this
initial object, so the inclusion |∂Δ[0]| → |Δ[0]| has empty range.

Its range complement is the whole realized zero-simplex. The complement subspace is therefore
homeomorphic to the ambient space, and the inverse direction gives a TopCat isomorphism from
the ambient space to that subspace. Its hom is the section into the full subspace and its inv
is inclusion.
-/

@[expose] public section

universe u

open CategoryTheory Limits Simplicial

namespace SSet

/-- Empty range of the realized zero-simplex boundary inclusion.

The map |∂Δ[0]| → |Δ[0]| has range ∅. Realization sends the initial simplicial boundary to an
initial, hence empty, topological space. -/
theorem realizedBoundaryZero_range_empty :
    Set.range (SSet.toTop.map (SSet.boundary.{u} (0 : ℕ)).ι).hom = ∅ := by
  have : PreservesColimits SSet.toTop.{u} :=
    _root_.sSetTopAdj.leftAdjoint_preservesColimits
  have hBot : SSet.boundary (0 : ℕ) = ⊥ := SSet.boundary_zero
  have hInitS : IsInitial ((SSet.boundary (0 : ℕ) : SSet.{u})) := by
    rw [hBot]
    exact SSet.Subcomplex.isInitialBot
  have hInitTop : IsInitial (SSet.toTop.obj ((SSet.boundary (0 : ℕ) : SSet.{u}))) :=
    hInitS.isInitialObj SSet.toTop _
  have hIso : SSet.toTop.obj ((SSet.boundary (0 : ℕ) : SSet.{u})) ≅
      (TopCat.of PEmpty : TopCat.{u}) :=
    hInitTop.uniqueUpToIso TopCat.isInitialPEmpty
  have hElim : ∀ x : ↑(SSet.toTop.obj ((SSet.boundary (0 : ℕ) : SSet.{u})) : TopCat.{u}),
      False := fun x =>
    PEmpty.elim ((TopCat.homeoOfIso hIso) x)
  ext y
  simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
  rintro ⟨x, _⟩
  exact hElim x

/-- Full complement of the realized zero-boundary range.

Since the range of |∂Δ[0]| → |Δ[0]| is empty, its complement is the whole ambient realized
zero-simplex. -/
private theorem realizedBoundaryZero_compl_range_univ :
    (Set.range (SSet.toTop.map (SSet.boundary.{u} (0 : ℕ)).ι).hom)ᶜ =
      Set.univ := by
  rw [realizedBoundaryZero_range_empty, Set.compl_empty]

/-- Homeomorphism from the zero-boundary complement to the ambient realization.

The complement of the range of |∂Δ[0]| → |Δ[0]| is the whole space. Its subspace is
homeomorphic to |Δ[0]| by the full-subspace homeomorphism. -/
noncomputable def realizedBoundaryZeroComplSubspaceHomeo :
    (TopCat.of ↥((Set.range (SSet.toTop.map (SSet.boundary.{u} (0 : ℕ)).ι).hom)ᶜ)) ≃ₜ
      SSet.toTop.obj (Δ[0] : SSet.{u}) :=
  (Homeomorph.setCongr realizedBoundaryZero_compl_range_univ).trans (Homeomorph.Set.univ _)

/-- Isomorphism from the ambient zero-simplex to its boundary complement.

The homeomorphism of the complement subspace with |Δ[0]| gives, in the inverse direction, a
TopCat isomorphism |Δ[0]| ≅ complement. The hom is the full-subspace section and the inv is
inclusion. -/
noncomputable def realizedBoundaryZeroComplSubspaceIso :
    SSet.toTop.obj (Δ[0] : SSet.{u}) ≅
      TopCat.of ↥((Set.range (SSet.toTop.map (SSet.boundary.{u} (0 : ℕ)).ι).hom)ᶜ) :=
  (TopCat.isoOfHomeo realizedBoundaryZeroComplSubspaceHomeo).symm

end SSet

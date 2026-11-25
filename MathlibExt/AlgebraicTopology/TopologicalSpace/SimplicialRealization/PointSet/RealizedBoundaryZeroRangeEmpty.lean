/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Realized boundary-zero has empty range

The realized inclusion of `∂Δ[0]` has empty range: `SSet.boundary_zero`
identifies the zero boundary with `⊥`, `SSet.Subcomplex.isInitialBot` makes
it initial in `SSet`, realization preserves the initial object, and the
TopCat initial-object comparison (`uniqueUpToIso` with
`TopCat.isInitialPEmpty` transported by `TopCat.homeoOfIso`) supplies an
honest empty-domain elimination. The range emptiness follows by exhibiting
no domain inhabitant, not by assuming one impossible.

Nonclaims: no chart, cover, gluing, local-Serre, finite-base, or model
result. Direct consumer: zero-cell range/complement steps over the realized
boundary-zero inclusion.
-/

@[expose] public section

universe u

open CategoryTheory Limits Simplicial SSet

/-- The realized `∂Δ[0]` inclusion has empty range, via the initial-object
comparison. -/
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

/-- Complement corollary: the complement of the empty realized range is `univ`. -/
theorem realizedBoundaryZero_compl_range_univ :
    (Set.range (SSet.toTop.map (SSet.boundary.{u} (0 : ℕ)).ι).hom)ᶜ =
      Set.univ := by
  rw [realizedBoundaryZero_range_empty, Set.compl_empty]

/-- Homeomorphism from the complement-subspace to the ambient realized zero-simplex,
via the univ identification. -/
noncomputable def realizedBoundaryZeroComplSubspaceHomeo :
    (TopCat.of ↥((Set.range (SSet.toTop.map (SSet.boundary.{u} (0 : ℕ)).ι).hom)ᶜ)) ≃ₜ
      SSet.toTop.obj (Δ[0] : SSet.{u}) := by
  rw [realizedBoundaryZero_compl_range_univ]
  exact Homeomorph.Set.univ _

/-- TopCat isomorphism identifying the complement-subspace with the ambient
realized zero-simplex. Its hom is the section; its inv is the subspace inclusion. -/
noncomputable def realizedBoundaryZeroComplSubspaceIso :
    SSet.toTop.obj (Δ[0] : SSet.{u}) ≅
      TopCat.of ↥((Set.range (SSet.toTop.map (SSet.boundary.{u} (0 : ℕ)).ι).hom)ᶜ) :=
  (TopCat.isoOfHomeo realizedBoundaryZeroComplSubspaceHomeo).symm

/-- The section followed by the inclusion is the identity on the ambient. -/
theorem realizedBoundaryZeroComplSubspaceIso_hom_inv :
    realizedBoundaryZeroComplSubspaceIso.hom ≫
      realizedBoundaryZeroComplSubspaceIso.inv = 𝟙 _ :=
  Iso.hom_inv_id _

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationCompactSupport

/-!
# Compact-support finite-subcomplex consumer regressions

Direct symbolic, universe-one, and universe-zero consumers of
`SSet.exists_finite_subcomplex_of_isCompact`. They lock the finite witness's
universe and the containment direction. Singleton support in an infinite
coproduct prevents an overclaim that the ambient simplicial set is finite.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.CompactSupportTests

/-- Compact sets have support in a finite subcomplex at the same universe. -/
theorem compact_support_client
    (Y : SSet.{u}) (K : Set (SSet.toTop.obj Y)) (hK : IsCompact K) :
    ∃ (A : Y.Subcomplex) (_ : SSet.Finite (A : SSet.{u})),
      K ⊆ Set.range (SSet.toTop.map A.ι) :=
  SSet.exists_finite_subcomplex_of_isCompact Y K hK

/-- Universe-one support of the whole realized one-simplex. -/
theorem univ_mem_range_of_finite_subcomplex_Δ1_universeOne
    (x : SSet.toTop.obj (Δ[1] : SSet.{1})) :
    ∃ (A : (Δ[1] : SSet.{1}).Subcomplex)
      (_ : SSet.Finite (A : SSet.{1}))
      (y : SSet.toTop.obj (A : SSet.{1})),
      SSet.toTop.map A.ι y = x := by
  obtain ⟨A, hfin, hcover⟩ :=
    SSet.exists_finite_subcomplex_of_isCompact (Δ[1] : SSet.{1}) Set.univ
      isCompact_univ
  obtain ⟨y, hy⟩ := hcover (Set.mem_univ x)
  exact ⟨A, hfin, y, hy⟩

/-- Universe-one singleton support in an infinite coproduct of vertices. -/
theorem singleton_mem_range_of_finite_subcomplex_infinite_coproduct_universeOne
    (x : SSet.toTop.obj (∐ fun _ : ℕ => (Δ[0] : SSet.{1}))) :
    ∃ (A : (∐ fun _ : ℕ => (Δ[0] : SSet.{1})).Subcomplex)
      (_ : SSet.Finite (A : SSet.{1}))
      (y : SSet.toTop.obj (A : SSet.{1})),
      SSet.toTop.map A.ι y = x := by
  obtain ⟨A, hfin, hcover⟩ :=
    SSet.exists_finite_subcomplex_of_isCompact
      (∐ fun _ : ℕ => (Δ[0] : SSet.{1})) {x} isCompact_singleton
  obtain ⟨y, hy⟩ := hcover (Set.mem_singleton x)
  exact ⟨A, hfin, y, hy⟩

/-- Original universe-zero whole-simplex client. -/
theorem univ_mem_range_of_finite_subcomplex_Δ1
    (x : SSet.toTop.obj (Δ[1] : SSet.{0})) :
    ∃ (A : (Δ[1] : SSet.{0}).Subcomplex) (_ : SSet.Finite (A : SSet.{0}))
      (y : SSet.toTop.obj (A : SSet.{0})),
      SSet.toTop.map A.ι y = x := by
  obtain ⟨A, hfin, hcover⟩ :=
    SSet.exists_finite_subcomplex_of_isCompact (Δ[1] : SSet.{0}) Set.univ
      isCompact_univ
  obtain ⟨y, hy⟩ := hcover (Set.mem_univ x)
  exact ⟨A, hfin, y, hy⟩

/-- Original universe-zero singleton support in an infinite coproduct. -/
theorem singleton_mem_range_of_finite_subcomplex_infinite_coproduct
    (x : SSet.toTop.obj (∐ fun _ : ℕ => (Δ[0] : SSet.{0}))) :
    ∃ (A : (∐ fun _ : ℕ => (Δ[0] : SSet.{0})).Subcomplex)
      (_ : SSet.Finite (A : SSet.{0}))
      (y : SSet.toTop.obj (A : SSet.{0})),
      SSet.toTop.map A.ι y = x := by
  obtain ⟨A, hfin, hcover⟩ :=
    SSet.exists_finite_subcomplex_of_isCompact
      (∐ fun _ : ℕ => (Δ[0] : SSet.{0})) {x} isCompact_singleton
  obtain ⟨y, hy⟩ := hcover (Set.mem_singleton x)
  exact ⟨A, hfin, y, hy⟩

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.MeetsCarrier

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.selImg

#print axioms SSet.exists_finite_subcomplex_of_isCompact
#print axioms compact_support_client
#print axioms univ_mem_range_of_finite_subcomplex_Δ1_universeOne
#print axioms singleton_mem_range_of_finite_subcomplex_infinite_coproduct_universeOne
#print axioms univ_mem_range_of_finite_subcomplex_Δ1
#print axioms singleton_mem_range_of_finite_subcomplex_infinite_coproduct

end MathlibExtTest.AlgebraicTopology.ModelCategory.CompactSupportTests

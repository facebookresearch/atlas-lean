/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexAttachmentCompat
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Boundary
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbedding
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedT1Embedding

/-!
# Realized simplex attachments and closed embeddings

A cellular attachment to the boundary of `Δ[N]` realizes as a `TopCat` pushout with
full-simplex apex. Boundary maximality (`SSet.stdSimplex.le_boundary_iff`) identifies
the apex, and the missing-cell dimension bound fixes the attachment dimension to `N`.
The functor `SSet.toTop` preserves the pushout via `sSetTopAdj`; the realized boundary
closed embedding, supplied by `SSet.boundary.closedT1Embeddings_toTop_map_ι` and
`TopCat.closedT1Embeddings_le_isClosedEmbedding`, gives a closed embedding of the old
leg by `TopCat.isClosedEmbedding_of_isPushout`. Comparing the attaching-map complement
with the barycenter complement requires explicit boundary-range and openness data.
-/

@[expose] public section

universe u

open CategoryTheory Limits Simplicial SSet Topology

/-- Realized simplex-cell pushout with apex `⊤`.

For ambient `N`, the generic cellular step applied to `A = ∂Δ[N]` yields some
attachment dimension `m`, some `B` with `A < B`, and a `TopCat` pushout from
the realized boundary inclusion. The apex satisfies `B = ⊤` by boundary
maximality. The attachment dimension `m` is existential in this statement;
`realizedSimplexCellPushout_fixedIndex` identifies it with `N`. -/
theorem realizedSimplexCellPushout (N : ℕ) :
    ∃ (m : ℕ) (B : ((Δ[N] : SSet.{u}).Subcomplex))
      (t : SSet.toTop.obj (SSet.boundary.{u} m : SSet.{u}) ⟶
        SSet.toTop.obj ((SSet.boundary.{u} N : ((Δ[N] : SSet.{u}).Subcomplex)) : SSet.{u}))
      (r : SSet.toTop.obj ((SSet.boundary.{u} N : ((Δ[N] : SSet.{u}).Subcomplex)) : SSet.{u}) ⟶
        SSet.toTop.obj (B : SSet.{u}))
      (b : SSet.toTop.obj (Δ[m] : SSet.{u}) ⟶ SSet.toTop.obj (B : SSet.{u})),
      IsPushout t (SSet.toTop.map (SSet.boundary.{u} m).ι) r b ∧ B = ⊤ := by
  classical
  have hA_ne : SSet.boundary.{u} N ≠ ⊤ := ne_of_lt (SSet.boundary_lt_top N)
  obtain ⟨B, hlt, m, t, b, hPush⟩ :=
    SSet.boundary.exists_isPushout_of_ne_top (X := (Δ[N] : SSet.{u}))
      (SSet.boundary.{u} N) hA_ne
  have h_not_le : ¬ B ≤ SSet.boundary.{u} N := by
    intro h_le
    have h_eq : SSet.boundary.{u} N = B := le_antisymm (le_of_lt hlt) h_le
    exact (ne_of_lt hlt) h_eq
  have hB_top : B = ⊤ := by
    by_contra h_ne
    have h_le : B ≤ SSet.boundary.{u} N :=
      (SSet.stdSimplex.le_boundary_iff B).mpr h_ne
    exact h_not_le h_le
  have : PreservesColimits SSet.toTop.{u} :=
    _root_.sSetTopAdj.leftAdjoint_preservesColimits
  have hPushTop :
      IsPushout (SSet.toTop.map t) (SSet.toTop.map (SSet.boundary.{u} m).ι)
        (SSet.toTop.map (SSet.Subcomplex.homOfLE (le_of_lt hlt)))
        (SSet.toTop.map b) :=
    hPush.map SSet.toTop.{u}
  exact ⟨m, B, _, _, _, hPushTop, hB_top⟩

/-- Realized simplex-cell pushout with fixed attachment index `N`.

For ambient `N`, the witness-carrying cellular step applied to `A = ∂Δ[N]`
exposes the attachment dimension `m` with a missing nondegenerate `m`-cell
outside the boundary. Since `Δ[N]` has dimension `≤ N`
(`SSet.dim_le_of_nonDegenerate`), `m ≤ N`; since the boundary is full below
`N` (`SSet.boundary_obj_eq_univ`), `m < N` is impossible. Hence `m = N`;
transport along that equality fixes the attachment index. Index orientation:
`m` is the attached standard-simplex dimension, `N` is the ambient dimension. -/
theorem realizedSimplexCellPushout_fixedIndex (N : ℕ) :
    ∃ (B : ((Δ[N] : SSet.{u}).Subcomplex))
      (t : SSet.toTop.obj (SSet.boundary.{u} N : SSet.{u}) ⟶
        SSet.toTop.obj ((SSet.boundary.{u} N : ((Δ[N] : SSet.{u}).Subcomplex)) : SSet.{u}))
      (r : SSet.toTop.obj ((SSet.boundary.{u} N : ((Δ[N] : SSet.{u}).Subcomplex)) : SSet.{u}) ⟶
        SSet.toTop.obj (B : SSet.{u}))
      (b : SSet.toTop.obj (Δ[N] : SSet.{u}) ⟶ SSet.toTop.obj (B : SSet.{u})),
      IsPushout t (SSet.toTop.map (SSet.boundary.{u} N).ι) r b ∧ B = ⊤ := by
  classical
  have h_lt : (SSet.boundary.{u} N : ((Δ[N] : SSet.{u}).Subcomplex)) < ⊤ :=
    SSet.boundary_lt_top N
  obtain ⟨B, hAB, _, m, x, _, hxA, _, _, t0, b0, hPush0⟩ :=
    SSet.boundary.exists_isPushout_of_lt_with_witness
      (X := (Δ[N] : SSet.{u})) (SSet.boundary.{u} N) ⊤ h_lt
  have h_le : m ≤ N := ((Δ[N] : SSet.{u}).dim_le_of_nonDegenerate x N)
  have h_not_lt : ¬ m < N := by
    intro hlt
    have hmem : x.1 ∈ ((SSet.boundary.{u} N : ((Δ[N] : SSet.{u}).Subcomplex)).obj
        (Opposite.op ⦋m⦌)) := by
      rw [SSet.boundary_obj_eq_univ m N hlt]
      exact Set.mem_univ _
    exact hxA hmem
  have h_eq : m = N := le_antisymm h_le (le_of_not_gt h_not_lt)
  subst m
  have h_not_le : ¬ B ≤ SSet.boundary.{u} N := by
    intro h_le'
    have h_eq' : SSet.boundary.{u} N = B := le_antisymm (le_of_lt hAB) h_le'
    exact (ne_of_lt hAB) h_eq'
  have hB_top : B = ⊤ := by
    by_contra h_ne
    have h_le' : B ≤ SSet.boundary.{u} N :=
      (SSet.stdSimplex.le_boundary_iff B).mpr h_ne
    exact h_not_le h_le'
  have : PreservesColimits SSet.toTop.{u} :=
    _root_.sSetTopAdj.leftAdjoint_preservesColimits
  have hPushTop :
      IsPushout (SSet.toTop.map t0) (SSet.toTop.map (SSet.boundary.{u} N).ι)
        (SSet.toTop.map (SSet.Subcomplex.homOfLE (le_of_lt hAB)))
        (SSet.toTop.map b0) :=
    hPush0.map SSet.toTop.{u}
  exact ⟨B, _, _, _, hPushTop, hB_top⟩

/-- The old leg of a realized simplex-cell pushout is a closed embedding.

Given any `TopCat` pushout whose left leg is a realized boundary inclusion,
the right leg is a closed embedding by pushout stability. -/
theorem isClosedEmbedding_simplexCell_oldLeg
    {m : ℕ} {X P : TopCat.{u}}
    {t : SSet.toTop.obj (SSet.boundary.{u} m : SSet.{u}) ⟶ X}
    {r : X ⟶ P} {b : SSet.toTop.obj (Δ[m] : SSet.{u}) ⟶ P}
    (hPush : IsPushout t (SSet.toTop.map (SSet.boundary.{u} m).ι) r b) :
    IsClosedEmbedding r.hom := by
  have hl : IsClosedEmbedding (SSet.toTop.map (SSet.boundary.{u} m).ι).hom :=
    TopCat.closedT1Embeddings_le_isClosedEmbedding _
      (SSet.boundary.closedT1Embeddings_toTop_map_ι.{u} m)
  exact TopCat.isClosedEmbedding_of_isPushout hPush.flip hl

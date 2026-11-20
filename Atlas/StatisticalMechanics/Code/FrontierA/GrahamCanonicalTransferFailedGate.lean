/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamCanonicalTransferQuadrangle










open Finset
open scoped symmDiff

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

private theorem symmDiff_subset_of_subsets_failed
    {A B S : Finset I} (hA : A ⊆ S) (hB : B ⊆ S) : A ∆ B ⊆ S := by
  intro i hi
  rcases Finset.mem_symmDiff.mp hi with hi | hi
  · exact hA hi.1
  · exact hB hi.1


theorem edgeComponent_eq_of_conn
    (ends : I -> Sym2 W) (K : Finset I) (u v : W)
    (huv : connK ends K u v) :
    edgeComponent ends K u = edgeComponent ends K v := by
  classical
  ext i
  constructor
  · intro hi
    rw [edgeComponent, Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, ?_⟩
    intro x hx
    exact (connK_symm ends K huv).trans (hi.2 x hx)
  · intro hi
    rw [edgeComponent, Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, ?_⟩
    intro x hx
    exact huv.trans (hi.2 x hx)



theorem component_eq_of_not_rowsDisconnect
    (ends : I -> Sym2 W) (m : Finset I) (c : ↑m -> Fin 4)
    (k zero : W) (hbad : ¬ RowsDisconnect ends m c k zero) :
    edgeComponent ends (rowClass m c 0) zero =
        edgeComponent ends (rowClass m c 0) k ∨
      edgeComponent ends (rowClass m c 1) zero =
        edgeComponent ends (rowClass m c 1) k := by
  by_cases hzero : connK ends (rowClass m c 0) k zero
  · exact Or.inl (edgeComponent_eq_of_conn
      ends (rowClass m c 0) k zero hzero).symm
  · have hone : connK ends (rowClass m c 1) k zero := by
      by_contra hone
      exact hbad ⟨hzero, hone⟩
    exact Or.inr (edgeComponent_eq_of_conn
      ends (rowClass m c 1) k zero hone).symm



theorem canonicalQuadrangleCompletion_failedGate_component
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b c : ↑m -> Fin 4)
    (hbad : ¬ RowsDisconnect ends m
      (canonicalQuadrangleCompletion ends m k zero a b c) k zero) :
    let d := canonicalQuadrangleCompletion ends m k zero a b c
    edgeComponent ends (rowClass m d 0) zero =
        edgeComponent ends (rowClass m d 0) k ∨
      edgeComponent ends (rowClass m d 1) zero =
        edgeComponent ends (rowClass m d 1) k := by
  exact component_eq_of_not_rowsDisconnect ends m
    (canonicalQuadrangleCompletion ends m k zero a b c) k zero hbad



theorem canonicalQuadrangleCompletion_rowBoundaries
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p) :
    let d := canonicalQuadrangleCompletion ends m k zero
      a.1.1 b.1.1 c.1.1;
    sources ends (rowClass m d 0) = {j, k} ∧
      sources ends (rowClass m d 1) = {k, l} := by
  dsimp only
  let X := canonicalMiddleTransferDifference ends m k zero a.1.1 b.1.1
  let Y := canonicalOuterTransferDifference ends m k zero a.1.1 b.1.1
  let d := canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1
  have hva := canonicalTransfers_valid_on_sameMask hloop hjk hkl a c
  have hvb := canonicalTransfers_valid_on_sameMask hloop hjk hkl b c
  have hX : X ⊆ colorClass m c.1.1 1 ∪ colorClass m c.1.1 2 := by
    dsimp only [X, canonicalMiddleTransferDifference]
    exact symmDiff_subset_of_subsets_failed hva.1 hvb.1
  have hY : Y ⊆ colorClass m c.1.1 0 ∪ colorClass m c.1.1 3 := by
    dsimp only [Y, canonicalOuterTransferDifference]
    exact symmDiff_subset_of_subsets_failed hva.2.1 hvb.2.1
  have hXmask : X ⊆ middleMask m c.1.1 := by
    simpa only [middleMask] using hX
  have hYmask : Y ⊆ outerMask m c.1.1 := by
    simpa only [outerMask] using hY
  have hXY : Disjoint X Y :=
    (middleMask_disjoint_outerMask m c.1.1).mono hXmask hYmask
  have hsrcX : sources ends X = ∅ := by
    dsimp only [X, canonicalMiddleTransferDifference]
    rw [sources_symmDiff, hva.2.2.1, hvb.2.2.1]
    exact symmDiff_self _
  have hsrcY : sources ends Y = ∅ := by
    dsimp only [Y, canonicalOuterTransferDifference]
    rw [sources_symmDiff, hva.2.2.2, hvb.2.2.2]
    exact symmDiff_self _
  have hsrcXY : sources ends (X ∪ Y) = ∅ := by
    rw [sources_union_of_disjoint hXY, hsrcX, hsrcY]
    simp
  have hcRows := leftPattern_rowBoundaries c.1.2
  have hrow0 : rowClass m d 0 = rowClass m c.1.1 0 ∆ (X ∪ Y) := by
    dsimp only [d, canonicalQuadrangleCompletion]
    exact rowClass_balancedSwap_zero hX hY
  have hrow1 : rowClass m d 1 = rowClass m c.1.1 1 ∆ (X ∪ Y) := by
    dsimp only [d, canonicalQuadrangleCompletion]
    exact rowClass_balancedSwap_one hX hY
  constructor
  · rw [hrow0, sources_symmDiff, hcRows.1, hsrcXY]
    simp
  · rw [hrow1, sources_symmDiff, hcRows.2, hsrcXY]
    simp

private theorem edgeComponent_subset_support
    (ends : I -> Sym2 W) (K : Finset I) (u : W) :
    edgeComponent ends K u ⊆ K := by
  classical
  intro i hi
  rw [edgeComponent, Finset.mem_filter] at hi
  exact hi.1



theorem failedRowZero_component_boundary
    {ends : I -> Sym2 W} {m : Finset I} {j k zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (d : ↑m -> Fin 4)
    (hsrc : sources ends (rowClass m d 0) = {j, k})
    (hconn : connK ends (rowClass m d 0) k zero) :
    sources ends (edgeComponent ends (rowClass m d 0) zero) = {j, k} ∧
      sources ends (rowClass m d 0 \
        edgeComponent ends (rowClass m d 0) zero) = ∅ := by
  have hjkConn : connK ends (rowClass m d 0) j k := by
    apply StatMech.Walls.gc6_pairingPath_abstract ends
      (rowClass m d 0) (rowClass m d 0)
    · intro i hi
      exact hloop i (by
        rw [rowClass_zero] at hi
        rcases Finset.mem_union.mp hi with hi | hi
        · exact colorClass_subset m d 0 hi
        · exact colorClass_subset m d 1 hi)
    · exact Finset.Subset.rfl
    · exact hsrc
    · exact hjk
  have hcompSrc : sources ends
      (edgeComponent ends (rowClass m d 0) zero) = {j, k} := by
    rw [sources_edgeComponent, hsrc]
    apply Finset.inter_eq_left.mpr
    intro x hx
    rw [mem_compOf]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (connK_symm ends _ hconn).trans
        (connK_symm ends _ hjkConn)
    · exact connK_symm ends _ hconn
  refine ⟨hcompSrc, ?_⟩
  rw [sources_sdiff_of_subset
      (edgeComponent_subset_support ends (rowClass m d 0) zero),
    hsrc, hcompSrc, symmDiff_self]
  rfl


theorem failedRowOne_component_boundary
    {ends : I -> Sym2 W} {m : Finset I} {k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hkl : k ≠ l) (d : ↑m -> Fin 4)
    (hsrc : sources ends (rowClass m d 1) = {k, l})
    (hconn : connK ends (rowClass m d 1) k zero) :
    sources ends (edgeComponent ends (rowClass m d 1) zero) = {k, l} ∧
      sources ends (rowClass m d 1 \
        edgeComponent ends (rowClass m d 1) zero) = ∅ := by
  have hklConn : connK ends (rowClass m d 1) k l := by
    apply StatMech.Walls.gc6_pairingPath_abstract ends
      (rowClass m d 1) (rowClass m d 1)
    · intro i hi
      exact hloop i (by
        rw [rowClass_one] at hi
        rcases Finset.mem_union.mp hi with hi | hi
        · exact colorClass_subset m d 2 hi
        · exact colorClass_subset m d 3 hi)
    · exact Finset.Subset.rfl
    · exact hsrc
    · exact hkl
  have hcompSrc : sources ends
      (edgeComponent ends (rowClass m d 1) zero) = {k, l} := by
    rw [sources_edgeComponent, hsrc]
    apply Finset.inter_eq_left.mpr
    intro x hx
    rw [mem_compOf]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact connK_symm ends _ hconn
    · exact (connK_symm ends _ hconn).trans hklConn
  refine ⟨hcompSrc, ?_⟩
  rw [sources_sdiff_of_subset
      (edgeComponent_subset_support ends (rowClass m d 1) zero),
    hsrc, hcompSrc, symmDiff_self]
  rfl





theorem canonicalQuadrangleCompletion_failedGate_boundaryCertificate
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    (hbad : ¬ RowsDisconnect ends m
      (canonicalQuadrangleCompletion ends m k zero
        a.1.1 b.1.1 c.1.1) k zero) :
    let d := canonicalQuadrangleCompletion ends m k zero
      a.1.1 b.1.1 c.1.1
    (connK ends (rowClass m d 0) k zero ∧
        sources ends (edgeComponent ends (rowClass m d 0) zero) = {j, k} ∧
        sources ends (rowClass m d 0 \
          edgeComponent ends (rowClass m d 0) zero) = ∅) ∨
      (connK ends (rowClass m d 1) k zero ∧
        sources ends (edgeComponent ends (rowClass m d 1) zero) = {k, l} ∧
        sources ends (rowClass m d 1 \
          edgeComponent ends (rowClass m d 1) zero) = ∅) := by
  let d := canonicalQuadrangleCompletion ends m k zero
    a.1.1 b.1.1 c.1.1
  have hsrc := canonicalQuadrangleCompletion_rowBoundaries
    hloop hjk hkl a b c
  dsimp only at hsrc
  by_cases hzero : connK ends (rowClass m d 0) k zero
  · left
    exact ⟨hzero, failedRowZero_component_boundary
      hloop hjk d hsrc.1 hzero⟩
  · have hone : connK ends (rowClass m d 1) k zero := by
      by_contra hone
      exact hbad ⟨hzero, hone⟩
    right
    exact ⟨hone, failedRowOne_component_boundary
      hloop hkl d hsrc.2 hone⟩

end StatMech.GrahamGHS.FourColor

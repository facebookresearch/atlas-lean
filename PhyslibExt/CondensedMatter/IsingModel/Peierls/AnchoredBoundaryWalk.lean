/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Theta
public import PhyslibExt.CondensedMatter.IsingModel.Peierls.ClusterContourBijection

/-!
# Clusters as open clusters of indicator configurations, and anchored boundary walks

A connected cluster is the open cluster of the origin in its own bond indicator configuration,
and in two dimensions contours anchored on the positive horizontal axis give the Peierls count.

## i. Overview

The bond configuration that opens exactly the edges with both endpoints in `K` has open
subgraph `latticeOn K`, and for a connected cluster `K ∋ 0` its open cluster at the origin is `K`
itself, hence finite. In `d = 2`, if every cluster contour of length `ℓ` is traced by a closed
walk of length `ℓ` based at one of the sites `(j, 0)`, `j < ℓ`, decoded by a single map, the
encoding of `ClusterContourBijection` follows and so does long-range order.

## ii. Key results

- `indicatorConfig` : the bond configuration open exactly on the edges inside `K`.
- `cluster_indicatorConfig` : its open cluster at the origin is `K`.
- `ccb_AnchoredBoundaryWalkExists` : contours of length `ℓ` traced from the anchor row.
- `ccb_peierls_of_anchoredBoundaryWalk` : anchored walks for all `n, ℓ` give `μ⁺_n ≠ μ⁻_n` for
  large `β` in `d = 2`.

## iii. Table of contents

- A. Indicator configurations of clusters
- B. Anchored boundary walks in two dimensions

## iv. References

- R. Peierls, *On Ising's model of ferromagnetism*, Proc. Cambridge Philos. Soc. 32 (1936)
  477–481.
- R. B. Griffiths, *Peierls proof of spontaneous magnetization in a two-dimensional Ising
  ferromagnet*, Phys. Rev. 136 (1964) A437–A439.
- S. Friedli and Y. Velenik, *Statistical Mechanics of Lattice Systems*, Cambridge University
  Press (2017), Section 3.7.2.
-/

@[expose] public section

open Set Finset SimpleGraph
open StatMech.Ising

namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ## A. Indicator configurations of clusters -/

/-- The bond configuration that is open exactly on the edges with both endpoints in `K`. -/
noncomputable def indicatorConfig (K : Finset (Site d)) : ConfigSpace (Sym2 (Site d)) :=
  fun e => Sym2.lift ⟨fun x y => decide (x ∈ K ∧ y ∈ K), by
    intro x y; simp only [decide_eq_decide]; tauto⟩ e

@[simp] lemma indicatorConfig_mk (K : Finset (Site d)) (x y : Site d) :
    indicatorConfig K s(x, y) = decide (x ∈ K ∧ y ∈ K) := rfl

lemma openSubgraph_indicatorConfig (K : Finset (Site d)) :
    openSubgraph d (indicatorConfig K) = latticeOn (↑K : Set (Site d)) := by
  ext x y
  rw [openSubgraph_adj]
  show ((hypercubicLattice d).Adj x y ∧ indicatorConfig K s(x, y) = true) ↔
    (latticeOn (↑K : Set (Site d))).Adj x y
  rw [show (latticeOn (↑K : Set (Site d))).Adj x y ↔
    (hypercubicLattice d).Adj x y ∧ x ∈ (↑K : Set (Site d)) ∧ y ∈ (↑K : Set (Site d)) from Iff.rfl]
  simp only [indicatorConfig_mk, decide_eq_true_eq, Finset.mem_coe]

lemma cluster_indicatorConfig (K : Finset (Site d)) (hconn : IsConnectedCluster K) :
    cluster d (indicatorConfig K) (origin d) = (↑K : Set (Site d)) := by
  ext x
  rw [mem_cluster]
  constructor
  · intro hx
    rw [Connected, openSubgraph_indicatorConfig] at hx
    obtain ⟨w⟩ := hx
    have key : ∀ {a b : Site d}, (latticeOn (↑K : Set (Site d))).Walk a b → a ∈ K → b ∈ K := by
      intro a b w
      induction w with
      | nil => exact fun h => h
      | @cons a b c hab w ih => intro _; exact ih (by simpa using hab.2.2)
    exact key w hconn.1
  · intro hx
    rw [Connected, openSubgraph_indicatorConfig]
    exact hconn.2 x (by simpa using hx)

lemma cluster_indicatorConfig_finite (K : Finset (Site d)) (hconn : IsConnectedCluster K) :
    (cluster d (indicatorConfig K) (origin d)).Finite := by
  rw [cluster_indicatorConfig K hconn]
  exact K.finite_toSet

/-! ## B. Anchored boundary walks in two dimensions -/

/-- The anchor row `{(j, 0) : j < ℓ}` in `ℤ²`. -/
noncomputable def ccb_anchorRow (ℓ : ℕ) : Finset (Site 2) :=
  (Finset.range ℓ).image (fun j : ℕ => (![ (j : ℤ), 0] : Site 2))

lemma ccb_anchorRow_card (ℓ : ℕ) : (ccb_anchorRow ℓ).card ≤ ℓ := by
  unfold ccb_anchorRow
  exact le_trans Finset.card_image_le (by rw [Finset.card_range])

lemma mem_ccb_anchorRow {ℓ : ℕ} {v : Site 2} :
    v ∈ ccb_anchorRow ℓ ↔ ∃ j : ℕ, j < ℓ ∧ v = ![ (j : ℤ), 0] := by
  unfold ccb_anchorRow
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, Finset.mem_range.mp hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, Finset.mem_range.mpr hj, rfl⟩

/-- In `ℤ²`, every connected cluster in `Λ_n` with contour length `ℓ` has its contour decoded from a
closed walk of length `ℓ` based in the anchor row. -/
def ccb_AnchoredBoundaryWalkExists (n ℓ : ℕ) : Prop :=
  ∃ D : (Σ v : Site 2, (hypercubicLattice 2).Walk v v) → Finset (Sym2 (Site 2)),
    ∀ K ∈ ccb_contourFiber 2 n ℓ,
      ∃ v ∈ ccb_anchorRow ℓ, ∃ w : (hypercubicLattice 2).Walk v v,
        w.length = ℓ ∧ D ⟨v, w⟩ = crossEdges (↑K) (bondFinsetTouch 2 n)

lemma ccb_contourEncodingExists_of_anchoredBoundaryWalk (n ℓ : ℕ)
    (h : ccb_AnchoredBoundaryWalkExists n ℓ) :
    ccb_ContourEncodingExists 2 n ℓ := by
  obtain ⟨D, hD⟩ := h
  choose! v hv w hwlen hwdec using hD
  refine ccb_contourEncodingExists_of_decode (d := 2) n ℓ (ccb_anchorRow ℓ)
    (ccb_anchorRow_card ℓ) (fun K => ⟨v K, w K⟩) ?_ D ?_
  · intro K hK; exact ⟨hv K hK, hwlen K hK⟩
  · intro K hK; exact hwdec K hK

lemma ccb_anchoredBoundaryWalkExists_of_emptyFiber (n ℓ : ℕ)
    (hempty : ccb_contourFiber 2 n ℓ = ∅) :
    ccb_AnchoredBoundaryWalkExists n ℓ := by
  refine ⟨fun _ => ∅, ?_⟩
  intro K hK
  rw [hempty] at hK
  exact absurd hK (Finset.notMem_empty K)

lemma ccb_peierls_of_anchoredBoundaryWalk
    (h : ∀ (n ℓ : ℕ), ccb_AnchoredBoundaryWalkExists n ℓ) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      Ising.plusMeasure 2 n β 0 ≠ Ising.minusMeasure 2 n β 0 :=
  ccb_peierls_long_range_order_of_encoding (d := 2) le_rfl
    (fun n ℓ => ccb_contourEncodingExists_of_anchoredBoundaryWalk n ℓ (h n ℓ))

end Lattice

end StatMech

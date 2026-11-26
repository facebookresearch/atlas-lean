/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.Reduce
public import Mathlib.Tactic.FinCases
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Filter.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FiberForestSpanningTree

/-!
# Buffered fibres of boxes

Sites with the same residue modulo `4L + 1` have disjoint, well-separated boxes; in the upper-lines
configuration two such boxes still reconnect the cut, so a buffer alone does not give coarse
trifurcations.

## i. Overview

`bc76_bufferResVec L y` is the residue of `y` modulo `4L + 1` in each coordinate. Distinct sites
with equal residue differ by more than `4L` in some coordinate, so their `L`-boxes are disjoint with
a gap of `2L`. Edges of the fibre quotient away from a collapsed site lift to open edges. In the
upper-lines configuration, collapsing the boxes at `0` and `bc76_yBuf L` (`bc76_twoBoxGn`)
reconnects the lines at heights `1` and `3` after the origin is removed, so the origin is a coarse
trifurcation whose cut does not survive the buffer (`bc76_buffer_insufficient`).

## ii. Key results

- `bc76_bufferFiber_boxes_disjoint` : boxes of a buffered fibre are disjoint.
- `bc76_buffer_insufficient` : the buffer does not preserve the cut.

## iii. Table of contents

- A. Buffered residues
- B. Two collapsed boxes
- C. The upper-lines configuration

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Buffered residues -/

/-- The residue of `y` modulo `4L + 1` in each coordinate. -/
def bc76_bufferResVec (L : ℕ) (y : Site d) : Fin d → Fin (4 * L + 1) :=
  fun i => ⟨(y i % (4 * L + 1 : ℤ)).toNat, by
    have hpos : (0 : ℤ) < 4 * L + 1 := by positivity
    have h1 : 0 ≤ y i % (4 * L + 1 : ℤ) := Int.emod_nonneg _ (by positivity)
    have h2 : y i % (4 * L + 1 : ℤ) < 4 * L + 1 := Int.emod_lt_of_pos _ hpos
    omega⟩

lemma bc76_far_of_sameBufferResidue {L : ℕ} {y y' : Site d}
    (hres : bc76_bufferResVec L y = bc76_bufferResVec L y') (hne : y ≠ y') :
    ∃ i, 4 * L < ((y - y') i).natAbs := by
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ y' i := by
    by_contra h; simp only [not_exists, not_not] at h; exact hne (funext h)
  refine ⟨i, ?_⟩
  have hposZ : (0 : ℤ) < 4 * L + 1 := by positivity
  have hresi : (y i % (4 * L + 1 : ℤ)).toNat = (y' i % (4 * L + 1 : ℤ)).toNat := by
    have := congrArg (fun f => (f i).val) hres
    simpa [bc76_bufferResVec] using this
  have hnn1 : 0 ≤ y i % (4 * L + 1 : ℤ) := Int.emod_nonneg _ (by positivity)
  have hnn2 : 0 ≤ y' i % (4 * L + 1 : ℤ) := Int.emod_nonneg _ (by positivity)
  have hemodeq : y i % (4 * L + 1 : ℤ) = y' i % (4 * L + 1 : ℤ) := by omega
  have hdvd : (4 * L + 1 : ℤ) ∣ (y - y') i := by
    rw [Pi.sub_apply]
    have hmodeq : (y i - y' i) % (4 * L + 1 : ℤ) = 0 := by
      rw [Int.sub_emod, hemodeq, sub_self, Int.zero_emod]
    exact Int.dvd_of_emod_eq_zero hmodeq
  have hnz : (y - y') i ≠ 0 := by rw [Pi.sub_apply]; exact sub_ne_zero.mpr hi
  have hdvdabs : (4 * L + 1 : ℤ) ∣ |(y - y') i| := (dvd_abs _ _).mpr hdvd
  have hge : (4 * L + 1 : ℤ) ≤ |(y - y') i| := Int.le_of_dvd (abs_pos.mpr hnz) hdvdabs
  have hge' : (4 * L + 1 : ℤ) ≤ ((y - y') i).natAbs := by rwa [Int.abs_eq_natAbs] at hge
  have : (4 * L + 1 : ℕ) ≤ ((y - y') i).natAbs := by exact_mod_cast hge'
  omega

lemma bc76_bufferFiber_boxes_disjoint {L : ℕ} {y y' : Site d}
    (hres : bc76_bufferResVec L y = bc76_bufferResVec L y') (hne : y ≠ y') :
    Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y') := by
  obtain ⟨i, hi⟩ := bc76_far_of_sameBufferResidue hres hne
  exact bc64_boxAround_disjoint_of_farCoord i (by omega)

lemma bc76_bufferGap {L : ℕ} {y y' : Site d}
    (hres : bc76_bufferResVec L y = bc76_bufferResVec L y') (hne : y ≠ y') :
    ∃ i, ∀ x : Site d, ((x - y) i).natAbs ≤ L → 2 * L < ((x - y') i).natAbs := by
  obtain ⟨i, hi⟩ := bc76_far_of_sameBufferResidue hres hne
  refine ⟨i, fun x hx => ?_⟩
  have hsub : (y - y') i = (x - y') i - (x - y) i := by simp only [Pi.sub_apply]; ring
  have hle : ((y - y') i).natAbs ≤ ((x - y') i).natAbs + ((x - y) i).natAbs := by
    rw [hsub]; exact Int.natAbs_sub_le _ _
  omega

lemma bc76_fiberQuotEdge_lifts {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {c : Fin d → Fin (2 * L + 1)} {y s t : Site d} (hy : y ∈ bc73_fiber ω L R c)
    (hs : s ≠ y) (ht : t ≠ y) (hadj : (bc75_fiberQuot ω L R c).Adj s t) :
    ∃ p q, p ∉ bc61_boxAround d L y ∧ q ∉ bc61_boxAround d L y ∧
      bc75_collapseFiber ω L R c p = s ∧ bc75_collapseFiber ω L R c q = t ∧
      (openSubgraph d ω).Adj p q := by
  obtain ⟨_, p, q, hp, hq, hpq⟩ := hadj
  refine ⟨p, q, ?_, ?_, hp, hq, hpq⟩
  · intro hpbox
    exact hs (by rw [← hp]; exact bc75_collapseFiber_eq hy hpbox)
  · intro hqbox
    exact ht (by rw [← hq]; exact bc75_collapseFiber_eq hy hqbox)

/-! ## B. Two collapsed boxes -/

/-- The site `(4L + 1, 0)`. -/
def bc76_yBuf (L : ℕ) : Site 2 := bc57_pt (4 * (L : ℤ) + 1) 0

/-- Collapse the `L`-boxes around `0` and `bc76_yBuf L` to their centres. -/
noncomputable def bc76_twoBoxCollapse (L : ℕ) : Site 2 → Site 2 :=
  fun x => if x ∈ bc61_boxAround 2 L (0 : Site 2) then (0 : Site 2)
           else if x ∈ bc61_boxAround 2 L (bc76_yBuf L) then bc76_yBuf L
           else x

/-- The quotient of the upper-lines open subgraph by the two-box collapse. -/
noncomputable def bc76_twoBoxGn (L : ℕ) : SimpleGraph (Site 2) :=
  bc72_quotGraph (openSubgraph 2 bc60_upperLines) (bc76_twoBoxCollapse L)

lemma bc76_yBuf_box_disjoint (L : ℕ) :
    Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc76_yBuf L)) := by
  refine bc64_boxAround_disjoint_of_farCoord 0 ?_
  have hcoord : ((0 : Site 2) - bc76_yBuf L) 0 = -(4 * (L : ℤ) + 1) := by
    simp only [Pi.sub_apply, bc76_yBuf]; rw [bc57_pt_fst]; simp
  rw [hcoord, Int.natAbs_neg]
  have hval : (4 * (L : ℤ) + 1).natAbs = 4 * L + 1 := by
    have : (4 * (L : ℤ) + 1) = ((4 * L + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.natAbs_natCast]
  omega

lemma bc76_collapse_zero {L : ℕ} {x : Site 2} (hx : x ∈ bc61_boxAround 2 L (0 : Site 2)) :
    bc76_twoBoxCollapse L x = 0 := by unfold bc76_twoBoxCollapse; rw [ite_eq_left hx]

lemma bc76_collapse_buf {L : ℕ} {x : Site 2} (hx : x ∈ bc61_boxAround 2 L (bc76_yBuf L)) :
    bc76_twoBoxCollapse L x = bc76_yBuf L := by
  unfold bc76_twoBoxCollapse
  have hx0 : x ∉ bc61_boxAround 2 L (0 : Site 2) :=
    fun h => Finset.disjoint_left.mp (bc76_yBuf_box_disjoint L) h hx
  rw [ite_eq_right hx0, ite_eq_left hx]

lemma bc76_collapse_id {L : ℕ} {x : Site 2} (hx0 : x ∉ bc61_boxAround 2 L (0 : Site 2))
    (hxb : x ∉ bc61_boxAround 2 L (bc76_yBuf L)) : bc76_twoBoxCollapse L x = x := by
  unfold bc76_twoBoxCollapse; rw [ite_eq_right hx0, ite_eq_right hxb]

lemma bc76_pt_notMem_boxBuf_of_col {L : ℕ} {k h : ℤ} (hk : k < 3 * (L : ℤ) + 1) :
    bc57_pt k h ∉ bc61_boxAround 2 L (bc76_yBuf L) := by
  rw [bc61_mem_boxAround, mem_box]
  simp only [not_forall, not_le]
  refine ⟨0, ?_⟩
  simp only [Pi.sub_apply, bc76_yBuf]
  rw [bc57_pt_fst, bc57_pt_fst]
  have : (k - (4 * (L : ℤ) + 1)) = k - 4 * (L : ℤ) - 1 := by ring
  omega

lemma bc76_boxBuf_boundary_mem {L : ℕ} {h : ℤ} (hh : h.natAbs ≤ L) :
    bc57_pt (3 * (L : ℤ) + 1) h ∈ bc61_boxAround 2 L (bc76_yBuf L) := by
  rw [bc61_mem_boxAround, mem_box]
  intro i; fin_cases i
  · simp only [Pi.sub_apply, bc76_yBuf]
    change ((bc57_pt (3 * (L : ℤ) + 1) h) 0 - (bc57_pt (4 * (L : ℤ) + 1) 0) 0).natAbs ≤ L
    rw [bc57_pt_fst, bc57_pt_fst]
    have : (3 * (L : ℤ) + 1 - (4 * (L : ℤ) + 1)) = -(L : ℤ) := by ring
    rw [this, Int.natAbs_neg, Int.natAbs_natCast]
  · simp only [Pi.sub_apply, bc76_yBuf]
    change ((bc57_pt (3 * (L : ℤ) + 1) h) 1 - (bc57_pt (4 * (L : ℤ) + 1) 0) 1).natAbs ≤ L
    rw [bc57_pt_snd, bc57_pt_snd]; simpa using hh

lemma bc76_pt_ne_zero_of_height {k h : ℤ} (hh : 1 ≤ h) : bc57_pt k h ≠ (0 : Site 2) := by
  intro heq; rw [bc60_pt_eq_origin_iff] at heq; omega

/-! ## C. The upper-lines configuration -/

lemma bc76_line_adj_gn {L : ℕ} {h k : ℤ} (hh : 1 ≤ h)
    (hlo : (L : ℤ) < k) (hhi : k + 1 < 3 * (L : ℤ) + 1) :
    (bc76_twoBoxGn L).Adj (bc57_pt k h) (bc57_pt (k + 1) h) := by
  have hkid : bc76_twoBoxCollapse L (bc57_pt k h) = bc57_pt k h :=
    bc76_collapse_id (StatMech.Walls.bc61_pt_outside_boxAround hlo) (bc76_pt_notMem_boxBuf_of_col
        (by omega))
  have hk1id : bc76_twoBoxCollapse L (bc57_pt (k + 1) h) = bc57_pt (k + 1) h :=
    bc76_collapse_id (StatMech.Walls.bc61_pt_outside_boxAround (by omega))
        (bc76_pt_notMem_boxBuf_of_col hhi)
  have hne : bc57_pt k h ≠ bc57_pt (k + 1) h := by
    intro heq; have := congrArg (fun f => f 0) heq; simp only [bc57_pt_fst] at this; omega
  exact ⟨hne, bc57_pt k h, bc57_pt (k + 1) h, hkid, hk1id, ⟨bc57_pt_adj k h, bc60_open k hh⟩⟩

lemma bc76_line_reach_right {L : ℕ} {h : ℤ} (hh : 1 ≤ h) (j : ℕ)
    (hj : (L : ℤ) + 1 + (j : ℤ) < 3 * (L : ℤ) + 1) :
    ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
      ⟨bc57_pt ((L : ℤ) + 1) h, by simpa using bc76_pt_ne_zero_of_height hh⟩
      ⟨bc57_pt ((L : ℤ) + 1 + (j : ℤ)) h, by simpa using bc76_pt_ne_zero_of_height hh⟩ := by
  induction j with
  | zero =>
    have : (⟨bc57_pt ((L : ℤ) + 1 + ((0 : ℕ) : ℤ)) h, by simpa using bc76_pt_ne_zero_of_height hh⟩
        : ({(0 : Site 2)}ᶜ : Set (Site 2)))
        = ⟨bc57_pt ((L : ℤ) + 1) h, by simpa using bc76_pt_ne_zero_of_height hh⟩ := by
      apply Subtype.ext; simp
    rw [this]
  | succ i ih =>
    have hjcast : ((L : ℤ) + 1 + ((i + 1 : ℕ) : ℤ)) = (L : ℤ) + 1 + (i : ℤ) + 1 := by push_cast;
                                                                                        ring
    have hilt : (L : ℤ) + 1 + (i : ℤ) < 3 * (L : ℤ) + 1 := by push_cast at hj; omega
    have hstep : (bc76_twoBoxGn L).Adj (bc57_pt ((L : ℤ) + 1 + (i : ℤ)) h)
        (bc57_pt ((L : ℤ) + 1 + (i : ℤ) + 1) h) :=
      bc76_line_adj_gn hh (by omega) (by push_cast at hj ⊢; omega)
    have hstep' : ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Adj
        ⟨bc57_pt ((L : ℤ) + 1 + (i : ℤ)) h, by simpa using bc76_pt_ne_zero_of_height hh⟩
        ⟨bc57_pt ((L : ℤ) + 1 + (i : ℤ) + 1) h, by
          simpa using bc76_pt_ne_zero_of_height (k := (L : ℤ) + 1 + (i : ℤ) + 1) hh⟩ := hstep
    have hres := (ih hilt).trans hstep'.reachable
    have hcongr : (⟨bc57_pt ((L : ℤ) + 1 + (i : ℤ) + 1) h, by
          simpa using bc76_pt_ne_zero_of_height (k := (L : ℤ) + 1 + (i : ℤ) + 1) hh⟩
          : ({(0 : Site 2)}ᶜ : Set (Site 2)))
        = ⟨bc57_pt ((L : ℤ) + 1 + ((i + 1 : ℕ) : ℤ)) h, by
            simpa using bc76_pt_ne_zero_of_height hh⟩ := by
      apply Subtype.ext; simp only; rw [hjcast]
    rw [hcongr] at hres
    exact hres

lemma bc76_glue_adj {L : ℕ} {h : ℤ} (hh : 1 ≤ h) (hhL : h.natAbs ≤ L) :
    (bc76_twoBoxGn L).Adj (bc57_pt (3 * (L : ℤ)) h) (bc76_yBuf L) := by
  have h1id : bc76_twoBoxCollapse L (bc57_pt (3 * (L : ℤ)) h) = bc57_pt (3 * (L : ℤ)) h :=
    bc76_collapse_id (StatMech.Walls.bc61_pt_outside_boxAround (by omega))
        (bc76_pt_notMem_boxBuf_of_col (by omega))
  have h2buf : bc76_twoBoxCollapse L (bc57_pt (3 * (L : ℤ) + 1) h) = bc76_yBuf L :=
    bc76_collapse_buf (bc76_boxBuf_boundary_mem hhL)
  have hadj : (openSubgraph 2 bc60_upperLines).Adj (bc57_pt (3 * (L : ℤ)) h)
      (bc57_pt (3 * (L : ℤ) + 1) h) := ⟨bc57_pt_adj (3 * (L : ℤ)) h, bc60_open (3 * (L : ℤ)) hh⟩
  have hne : bc57_pt (3 * (L : ℤ)) h ≠ bc76_yBuf L := by
    intro heq
    have := congrArg (fun f => f 1) heq
    simp only [bc57_pt_snd, bc76_yBuf, bc57_pt_snd] at this
    omega
  exact ⟨hne, bc57_pt (3 * (L : ℤ)) h, bc57_pt (3 * (L : ℤ) + 1) h, h1id, h2buf, hadj⟩

lemma bc76_yBuf_ne_zero (L : ℕ) : bc76_yBuf L ≠ (0 : Site 2) := by
  intro heq; rw [bc76_yBuf, bc60_pt_eq_origin_iff] at heq; omega

lemma bc76_gnCut_reconnect_upperLines {L : ℕ} (hL : 3 ≤ L) :
    ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
      ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
      ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ := by
  set jn : ℕ := 2 * L - 1 with hjn
  have hjnval : (jn : ℤ) = 2 * (L : ℤ) - 1 := by
    rw [hjn]; have : 1 ≤ 2 * L := by omega
    push_cast [Nat.cast_sub this]; ring
  have hjcol : (L : ℤ) + 1 + (jn : ℤ) = 3 * (L : ℤ) := by rw [hjnval]; ring
  have hjlt : (L : ℤ) + 1 + (jn : ℤ) < 3 * (L : ℤ) + 1 := by rw [hjcol]; omega
  have hreach1 : ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
      ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
      ⟨bc57_pt (3 * (L : ℤ)) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ := by
    have := bc76_line_reach_right (h := 1) (by norm_num) jn hjlt
    simpa only [hjcol] using this
  have hreach3 : ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
      ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
      ⟨bc57_pt (3 * (L : ℤ)) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ := by
    have := bc76_line_reach_right (h := 3) (by norm_num) jn hjlt
    simpa only [hjcol] using this
  have hL1 : (1 : ℤ).natAbs ≤ L := by simp only [Int.natAbs_one]; omega
  have hL3 : (3 : ℤ).natAbs ≤ L := by rw [show (3 : ℤ).natAbs = 3 from rfl]; omega
  have hglue1 : ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Adj
      ⟨bc57_pt (3 * (L : ℤ)) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
      ⟨bc76_yBuf L, by simpa using bc76_yBuf_ne_zero L⟩ :=
    bc76_glue_adj (by norm_num) hL1
  have hglue3 : ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Adj
      ⟨bc76_yBuf L, by simpa using bc76_yBuf_ne_zero L⟩
      ⟨bc57_pt (3 * (L : ℤ)) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ :=
    (bc76_glue_adj (by norm_num) hL3).symm
  exact ((hreach1.trans hglue1.reachable).trans hglue3.reachable).trans hreach3.symm

lemma bc76_buffer_insufficient {L : ℕ} (hL : 3 ≤ L) :
    bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧
    Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc76_yBuf L)) ∧
    ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
      ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
      ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ :=
  ⟨bc67_upperLines_is_G_n_trifurcation hL, bc76_yBuf_box_disjoint L,
   bc76_gnCut_reconnect_upperLines hL⟩

lemma bc76_status :
    (∀ {L : ℕ} {y y' : Site d}, bc76_bufferResVec L y = bc76_bufferResVec L y' → y ≠ y' →
      (∃ i, 4 * L < ((y - y') i).natAbs) ∧
      (∃ i, ∀ x : Site d, ((x - y) i).natAbs ≤ L → 2 * L < ((x - y') i).natAbs)) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (c : Fin d → Fin (2 * L + 1)) (y s t : Site d),
      y ∈ bc73_fiber ω L R c → s ≠ y → t ≠ y → (bc75_fiberQuot ω L R c).Adj s t →
      ∃ p q, p ∉ bc61_boxAround d L y ∧ q ∉ bc61_boxAround d L y ∧
        bc75_collapseFiber ω L R c p = s ∧ bc75_collapseFiber ω L R c q = t ∧
        (openSubgraph d ω).Adj p q) ∧
    (∀ {L : ℕ}, 3 ≤ L →
      bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧
      Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc76_yBuf L)) ∧
      ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
        ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
        ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩) := by
  refine ⟨?_, ?_, ?_⟩
  · intro L y y' hres hne
    exact ⟨bc76_far_of_sameBufferResidue hres hne, bc76_bufferGap hres hne⟩
  · intro ω L R c y s t hy hs ht hadj; exact bc76_fiberQuotEdge_lifts hy hs ht hadj
  · intro L hL; exact bc76_buffer_insufficient hL

end StatMech.Walls

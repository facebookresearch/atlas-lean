/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Mathlib
import Code.Ising.PeierlsUncond

open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal

namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}







lemma pcc_contourLen_empty (B : Finset (Sym2 (Site d))) :
    contourLen (∅ : Set (Site d)) B = 0 := by
  unfold contourLen crossEdges
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e _
  induction e with
  | h x y => rw [crosses_mk]; simp


lemma pcc_empty_mem_clusterFamily (n : ℕ) :
    (∅ : Finset (Site d)) ∈ clusterFamily (d := d) n :=
  Finset.empty_mem_powerset _




lemma pcc_one_le_sum (n : ℕ) (β : ℝ) :
    (1 : ℝ) ≤ ∑ K ∈ clusterFamily (d := d) n,
        Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ)) := by
  have hemp : (∅ : Finset (Site d)) ∈ clusterFamily (d := d) n :=
    pcc_empty_mem_clusterFamily n
  have hcl0 : contourLen ((∅ : Finset (Site d)) : Set (Site d)) (bondFinsetTouch d n) = 0 := by
    have hco : ((∅ : Finset (Site d)) : Set (Site d)) = ∅ := by simp
    rw [hco]; exact pcc_contourLen_empty _
  have hle := Finset.single_le_sum
      (f := fun K : Finset (Site d) =>
        Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ)))
      (s := clusterFamily (d := d) n)
      (fun K _ => by positivity) hemp
  simp only [hcl0, Nat.cast_zero, mul_zero, Real.exp_zero] at hle
  exact hle






theorem pcc_not_contourCountBound :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → ¬ ContourCountBound d n β := by
  obtain ⟨β₀, hβ₀⟩ := exists_beta_peierlsBound_lt_half d
  refine ⟨β₀, fun n β hβ hCount => ?_⟩
  have h1 : (1 : ℝ) ≤ ∑ K ∈ clusterFamily (d := d) n,
      Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ)) := pcc_one_le_sum n β
  have h2 : peierlsBound d β < 1 / 2 := hβ₀ β hβ
  have hle : (1 : ℝ) ≤ peierlsBound d β := le_trans h1 hCount
  linarith










noncomputable def originClusterFamily (n : ℕ) : Finset (Finset (Site d)) :=
  (clusterFamily (d := d) n).filter (fun K => origin d ∈ K)

lemma pcc_mem_originClusterFamily {n : ℕ} {K : Finset (Site d)} :
    K ∈ originClusterFamily (d := d) n ↔ K ∈ clusterFamily (d := d) n ∧ origin d ∈ K := by
  unfold originClusterFamily; rw [Finset.mem_filter]



lemma pcc_minusClusterFinset_mem_originFamily {n : ℕ} (τ : {x // x ∈ box d n} → Bool)
    (ho : glue (plusField d) τ (origin d) = false) :
    minusClusterFinset τ ho ∈ originClusterFamily (d := d) n := by
  rw [pcc_mem_originClusterFamily]
  refine ⟨minusClusterFinset_mem_family τ ho, ?_⟩
  rw [minusClusterFinset, Set.Finite.mem_toFinset]
  exact origin_mem_minusCluster (origin d)







theorem pcc_probOriginMinus_le_sum_probContour_origin (n : ℕ) (β : ℝ) :
    probOriginMinus (plusField d) n (bondFinsetTouch d n) β 0
      ≤ ∑ K ∈ originClusterFamily (d := d) n,
          probContour (↑K) (plusField d) n (bondFinsetTouch d n) β := by
  classical
  unfold probOriginMinus probContour
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun τ _ => ?_)
  set g : Finset (Site d) → ℝ := fun K =>
    (if ContourEvent (↑K) (bondFinsetTouch d n) (glue (plusField d) τ)
      then fvProb (plusField d) n (bondFinsetTouch d n) β 0 τ else 0) with hg
  have hgnn : ∀ K ∈ originClusterFamily (d := d) n, 0 ≤ g K := by
    intro K _; rw [hg]; dsimp only; split
    · exact fvProb_nonneg _ _ _ _ _ _
    · exact le_refl 0
  by_cases ho : glue (plusField d) τ (origin d) = false
  · rw [if_pos ho]
    have hKmem : minusClusterFinset τ ho ∈ originClusterFamily (d := d) n :=
      pcc_minusClusterFinset_mem_originFamily τ ho
    have hev : ContourEvent (↑(minusClusterFinset τ ho)) (bondFinsetTouch d n)
        (glue (plusField d) τ) := by
      rw [minusClusterFinset_coe τ ho]; exact contourEvent_of_origin_minus n ho
    have hge : fvProb (plusField d) n (bondFinsetTouch d n) β 0 τ
        = g (minusClusterFinset τ ho) := by rw [hg]; dsimp only; rw [if_pos hev]
    rw [hge]
    exact Finset.single_le_sum hgnn hKmem
  · rw [if_neg ho]
    exact Finset.sum_nonneg hgnn

set_option maxHeartbeats 1000000 in












theorem pcc_probOriginMinus_le_sum_origin (n : ℕ) (β : ℝ) :
    probOriginMinus (plusField d) n (bondFinsetTouch d n) β 0
      ≤ ∑ K ∈ originClusterFamily (d := d) n,
          Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ)) := by
  refine le_trans (pcc_probOriginMinus_le_sum_probContour_origin n β) ?_
  apply Finset.sum_le_sum
  intro K hK
  have hKfam : K ∈ clusterFamily (d := d) n := (pcc_mem_originClusterFamily.mp hK).1
  have hKbox : (↑K : Set (Site d)) ⊆ box d n := clusterFamily_subset_box hKfam
  have hbound := contour_energy_bound n (↑K) hKbox (plusField d) (bondFinsetTouch d n) β
  exact hbound









def pcc_rayS (c : Fin d) (j : ℕ) : Site d := fun i => if i = c then (j : ℤ) else 0


lemma pcc_rayS_zero (c : Fin d) : pcc_rayS c 0 = origin d := by
  funext i; unfold pcc_rayS origin; simp


lemma pcc_rayS_mem_box_le (c : Fin d) (j m : ℕ) (h : j ≤ m) : pcc_rayS c j ∈ box d m := by
  intro i; unfold pcc_rayS; by_cases hh : i = c <;> simp [hh]; omega


lemma pcc_rayS_succ_not_mem_box (c : Fin d) (n : ℕ) : pcc_rayS c (n+1) ∉ box d n := by
  intro hmem; have := hmem c; unfold pcc_rayS at this; simp at this; omega


lemma pcc_rayS_adj (c : Fin d) (j : ℕ) :
    (hypercubicLattice d).Adj (pcc_rayS c j) (pcc_rayS c (j+1)) := by
  rw [hypercubicLattice_adj]
  rw [show (∑ i, ((pcc_rayS c j) i - (pcc_rayS c (j+1)) i).natAbs)
      = ∑ i : Fin d, (if i = c then (1:ℕ) else 0) from ?_]
  · rw [Finset.sum_ite_eq' Finset.univ c (fun _ => (1:ℕ))]; simp [Finset.mem_univ]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold pcc_rayS; by_cases h : i = c
    · subst h; simp
    · simp [h]




lemma pcc_rayEdge_mem_bondFinsetTouch (n : ℕ) (c : Fin d) (j : ℕ) (hj : j ≤ n) :
    s(pcc_rayS c j, pcc_rayS c (j+1)) ∈ bondFinsetTouch d n := by
  unfold bondFinsetTouch
  rw [Finset.mem_image]
  refine ⟨(pcc_rayS c j, pcc_rayS c (j+1)), ?_, rfl⟩
  unfold bondPairsTouch
  rw [Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨?_, ?_⟩, pcc_rayS_adj c j, Or.inl ?_⟩
  · rw [mem_boxFinset]; exact pcc_rayS_mem_box_le c j (n+1) (by omega)
  · rw [mem_boxFinset]; exact pcc_rayS_mem_box_le c (j+1) (n+1) (by omega)
  · exact pcc_rayS_mem_box_le c j n hj







lemma pcc_one_le_contourLen {n : ℕ} (hd : 1 ≤ d) {K : Finset (Site d)}
    (hKbox : (↑K : Set (Site d)) ⊆ box d n) (hoK : origin d ∈ K) :
    1 ≤ contourLen (↑K) (bondFinsetTouch d n) := by
  classical
  set c : Fin d := ⟨0, hd⟩ with hc
  set P : ℕ → Prop := fun j => pcc_rayS c j ∈ (↑K : Set (Site d)) with hP
  have hP0 : P 0 := by rw [hP]; dsimp only; rw [pcc_rayS_zero]; exact hoK
  have hPn1 : ¬ P (n+1) := by
    rw [hP]; dsimp only
    intro hmem
    exact pcc_rayS_succ_not_mem_box c n (hKbox hmem)
  have hexit : ∃ j, j ≤ n ∧ P j ∧ ¬ P (j+1) := by
    by_contra hcon
    push Not at hcon
    have key : ∀ k, k ≤ n + 1 → P k := by
      intro k
      induction k with
      | zero => intro _; exact hP0
      | succ i ih => intro hle; exact hcon i (by omega) (ih (by omega))
    exact hPn1 (key (n+1) (le_refl _))
  obtain ⟨j, hjn, hPj, hPj1⟩ := hexit
  have hcross : s(pcc_rayS c j, pcc_rayS c (j+1)) ∈ crossEdges (↑K) (bondFinsetTouch d n) := by
    unfold crossEdges
    rw [Finset.mem_filter]
    refine ⟨pcc_rayEdge_mem_bondFinsetTouch n c j hjn, ?_⟩
    rw [crosses_mk]
    constructor
    · intro _ hmem; exact hPj1 hmem
    · intro _; rw [hP] at hPj; exact hPj
  rw [contourLen, Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, ← Ne,
      ← Finset.nonempty_iff_ne_empty]
  exact ⟨_, hcross⟩













def OriginContourCountBound (d n : ℕ) (β : ℝ) : Prop :=
  ∑ K ∈ originClusterFamily (d := d) n,
      Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ))
    ≤ peierlsBound d β





theorem pcc_peierlsContourBound_of_origin (n : ℕ) (β : ℝ)
    (hCount : OriginContourCountBound d n β) :
    PeierlsContourBound d n β :=
  le_trans (pcc_probOriginMinus_le_sum_origin n β) hCount







theorem pcc_peierls_long_range_order_of_origin (hd : 2 ≤ d)
    (hCount : ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → OriginContourCountBound d n β) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      plusMeasure d n β 0 ≠ minusMeasure d n β 0 := by
  obtain ⟨β₀, hβ₀⟩ := hCount
  refine peierls_long_range_order' hd ⟨β₀, fun n β hβ => ?_⟩
  exact pcc_peierlsContourBound_of_origin n β (hβ₀ n β hβ)

end Ising

end StatMech

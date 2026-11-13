/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































import Mathlib
import Code.Ising.InfiniteVolume
import Code.Ising.PressureBCIndep
import Code.Ising.PressureFull
import Code.Lattice.BoxSurfaceVolume

open Finset Filter Topology

namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}






theorem psv_adj_unique_coord {x y : Site d}
    (h : (∑ i, (x i - y i).natAbs) = 1) :
    ∃ i : Fin d, (x i - y i).natAbs = 1 ∧ ∀ j, j ≠ i → x j = y j := by
  set f : Fin d → ℕ := fun i => (x i - y i).natAbs with hf
  have hsum : ∑ i, f i = 1 := h
  obtain ⟨i, hi⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; norm_num : ∑ i, f i ≠ 0)
  have hfi : f i = 1 := by
    have hle : f i ≤ ∑ j, f j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [hsum] at hle
    have hpos : 1 ≤ f i := Nat.one_le_iff_ne_zero.mpr hi.2
    omega
  refine ⟨i, hfi, ?_⟩
  intro j hj
  have hzero : ∑ k ∈ Finset.univ \ {i}, f k = 0 := by
    have hsplit : ∑ k, f k = (∑ k ∈ Finset.univ \ {i}, f k) + f i :=
      Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ i) f
    rw [hsum, hfi] at hsplit; omega
  have hjmem : j ∈ Finset.univ \ {i} := by
    rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ j, by simp [hj]⟩
  have hfj : f j = 0 := (Finset.sum_eq_zero_iff.mp hzero) j hjmem
  have : (x j - y j).natAbs = 0 := hfj
  omega



open Classical in



theorem psv_nbr_card_le (x : Site d) (T : Finset (Site d)) :
    (T.filter (fun y => (hypercubicLattice d).Adj x y)).card ≤ 2 * d := by
  set S : Finset (Site d) :=
    ((Finset.univ : Finset (Fin d)) ×ˢ ({-1, 1} : Finset ℤ)).image
      (fun p => Function.update x p.1 (x p.1 + p.2)) with hS
  have hsub : T.filter (fun y => (hypercubicLattice d).Adj x y) ⊆ S := by
    intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨_, hadj⟩ := hy
    rw [hypercubicLattice_adj] at hadj
    obtain ⟨i, hi1, hrest⟩ := psv_adj_unique_coord hadj
    rw [hS, Finset.mem_image]
    refine ⟨(i, y i - x i), ?_, ?_⟩
    · rw [Finset.mem_product]
      refine ⟨Finset.mem_univ _, ?_⟩
      have : (x i - y i).natAbs = 1 := hi1
      rw [Finset.mem_insert, Finset.mem_singleton]; omega
    · funext k
      by_cases hk : k = i
      · subst hk; rw [Function.update_self]; ring
      · rw [Function.update_of_ne hk]; exact hrest k hk
  calc (T.filter (fun y => (hypercubicLattice d).Adj x y)).card
      ≤ S.card := Finset.card_le_card hsub
    _ ≤ ((Finset.univ : Finset (Fin d)) ×ˢ ({-1, 1} : Finset ℤ)).card := Finset.card_image_le
    _ = (Finset.univ : Finset (Fin d)).card * ({-1, 1} : Finset ℤ).card :=
        Finset.card_product _ _
    _ ≤ 2 * d := by
        rw [Finset.card_univ, Fintype.card_fin]
        have h2 : ({-1, 1} : Finset ℤ).card ≤ 2 :=
          le_trans (Finset.card_insert_le _ _) (by simp)
        calc d * ({-1, 1} : Finset ℤ).card ≤ d * 2 := Nat.mul_le_mul_left _ h2
          _ = 2 * d := by ring






theorem psv_volume_card (d n : ℕ) : (boxFinset d n).card = (2 * n + 1) ^ d := by
  have : boxFinset d n = boxSV_boxF d n := by rw [boxSV_boxF_eq_toFinset]; rfl
  rw [this, boxSV_card_boxF]

theorem psv_volume_card_real (d n : ℕ) :
    ((boxFinset d n).card : ℝ) = (2 * (n : ℝ) + 1) ^ d := by
  rw [psv_volume_card]; push_cast; ring




noncomputable def psv_Bdry (d n : ℕ) : Finset (Site d) :=
  (vertexBoundary_finite d (n + 1)).toFinset

theorem psv_mem_Bdry {n : ℕ} {x : Site d} :
    x ∈ psv_Bdry d n ↔ x ∈ box d (n + 1) ∧ x ∉ box d n := by
  unfold psv_Bdry
  rw [Set.Finite.mem_toFinset, mem_vertexBoundary]
  simp only [Nat.add_sub_cancel]

theorem psv_Bdry_card_val (d n : ℕ) :
    (psv_Bdry d n).card = (2 * (n + 1) + 1) ^ d - (2 * (n + 1) - 1) ^ d := by
  have h1 : (psv_Bdry d n).card = boxSV_boundaryCard d (n + 1) := by
    rw [psv_Bdry, boxSV_boundaryCard]
  rw [h1, boxSV_boundary_card d (n + 1) (by omega)]



theorem psv_Bdry_card_real_le (d n : ℕ) :
    ((psv_Bdry d n).card : ℝ) ≤ 2 * (d * (2 * (n : ℝ) + 3) ^ (d - 1)) := by
  rw [psv_Bdry_card_val]
  have hle : (2 * (n + 1) - 1) ^ d ≤ (2 * (n + 1) + 1) ^ d := Nat.pow_le_pow_left (by omega) d
  rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow]
  have hb1 : ((2 * (n + 1) + 1 : ℕ) : ℝ) = 2 * (n : ℝ) + 3 := by push_cast; ring
  have hb2 : ((2 * (n + 1) - 1 : ℕ) : ℝ) = 2 * (n : ℝ) + 1 := by
    have : (1 : ℕ) ≤ 2 * (n + 1) := by omega
    rw [Nat.cast_sub this]; push_cast; ring
  rw [hb1, hb2]
  have hpow := boxSV_pow_sub_pow_le (2 * (n : ℝ) + 3) (2 * (n : ℝ) + 1)
    (by positivity) (by linarith) d
  calc (2 * (n : ℝ) + 3) ^ d - (2 * (n : ℝ) + 1) ^ d
      ≤ ((2 * (n : ℝ) + 3) - (2 * (n : ℝ) + 1)) * (d * (2 * (n : ℝ) + 3) ^ (d - 1)) := hpow
    _ = 2 * (d * (2 * (n : ℝ) + 3) ^ (d - 1)) := by ring





theorem psv_diff_char (n : ℕ) {p : Site d × Site d}
    (hp : p ∈ bondPairsTouch d n \ bondPairsInternal d n) :
    (hypercubicLattice d).Adj p.1 p.2 ∧
    ((p.1 ∈ box d n ∧ p.2 ∈ box d (n + 1) ∧ p.2 ∉ box d n) ∨
     (p.2 ∈ box d n ∧ p.1 ∈ box d (n + 1) ∧ p.1 ∉ box d n)) := by
  rw [Finset.mem_sdiff] at hp
  obtain ⟨htouch, hint⟩ := hp
  unfold bondPairsTouch at htouch
  rw [Finset.mem_filter, Finset.mem_product, mem_boxFinset, mem_boxFinset] at htouch
  obtain ⟨⟨h1box, h2box⟩, hadj, hor⟩ := htouch
  refine ⟨hadj, ?_⟩
  unfold bondPairsInternal at hint
  rw [Finset.mem_filter, Finset.mem_product, mem_boxFinset, mem_boxFinset] at hint
  push Not at hint
  rcases hor with h1 | h2
  · left; exact ⟨h1, h2box, fun hc => (hint ⟨h1, hc⟩) hadj⟩
  · right; exact ⟨h2, h1box, fun hc => (hint ⟨hc, h2⟩) hadj⟩

open Classical in




theorem psv_ordered_diff_le (n : ℕ) :
    (bondPairsTouch d n \ bondPairsInternal d n).card ≤
      (((psv_Bdry d n) ×ˢ (boxFinset d (n + 1))).filter
        (fun q => (hypercubicLattice d).Adj q.1 q.2)).card * 2 := by
  set Filt := ((psv_Bdry d n) ×ˢ (boxFinset d (n + 1))).filter
      (fun q => (hypercubicLattice d).Adj q.1 q.2) with hFilt
  set Tgt := Filt ×ˢ (Finset.univ : Finset Bool) with hTgt
  have hcard : Tgt.card = Filt.card * 2 := by
    rw [hTgt, Finset.card_product, Finset.card_univ, Fintype.card_bool]
  rw [← hcard]
  apply Finset.card_le_card_of_injOn
    (fun p => ((if p.1 ∈ box d n then p.2 else p.1, if p.1 ∈ box d n then p.1 else p.2),
               decide (p.1 ∈ box d n)))
  · 
    intro p hp
    obtain ⟨hadj, hcase⟩ := psv_diff_char n hp
    rw [Finset.mem_coe, hTgt, Finset.mem_product]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [hFilt, Finset.mem_filter, Finset.mem_product]
    rcases hcase with ⟨h1n, h2box, h2nn⟩ | ⟨h2n, h1box, h1nn⟩
    · simp only [if_pos h1n]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [psv_mem_Bdry]; exact ⟨h2box, h2nn⟩
      · rw [mem_boxFinset]; exact box_subset_succ d n h1n
      · exact (hypercubicLattice d).symm hadj
    · simp only [if_neg h1nn]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [psv_mem_Bdry]; exact ⟨h1box, h1nn⟩
      · rw [mem_boxFinset]; exact box_subset_succ d n h2n
      · exact hadj
  · 
    intro p _ q _ heq
    simp only [Prod.mk.injEq, decide_eq_decide] at heq
    obtain ⟨⟨hb, ha⟩, hside⟩ := heq
    by_cases hp1 : p.1 ∈ box d n
    · have hq1 : q.1 ∈ box d n := hside.mp hp1
      rw [if_pos hp1, if_pos hq1] at hb ha
      exact Prod.ext ha hb
    · have hq1 : q.1 ∉ box d n := fun h => hp1 (hside.mpr h)
      rw [if_neg hp1, if_neg hq1] at hb ha
      exact Prod.ext hb ha

open Classical in

theorem psv_filt_card_le (n : ℕ) :
    (((psv_Bdry d n) ×ˢ (boxFinset d (n + 1))).filter
        (fun q => (hypercubicLattice d).Adj q.1 q.2)).card
      ≤ (psv_Bdry d n).card * (2 * d) := by
  have heq : ((psv_Bdry d n) ×ˢ (boxFinset d (n + 1))).filter
        (fun q => (hypercubicLattice d).Adj q.1 q.2)
      = (psv_Bdry d n).biUnion
          (fun b => ({b} ×ˢ ((boxFinset d (n + 1)).filter
            (fun y => (hypercubicLattice d).Adj b y)))) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨p.1, h1, rfl, h2, h3⟩
    · rintro ⟨b, hb, hp1, hp2, hp3⟩; subst hp1; exact ⟨⟨hb, hp2⟩, hp3⟩
  rw [heq]
  calc ((psv_Bdry d n).biUnion
          (fun b => ({b} ×ˢ ((boxFinset d (n + 1)).filter
            (fun y => (hypercubicLattice d).Adj b y))))).card
      ≤ ∑ b ∈ psv_Bdry d n,
          ({b} ×ˢ ((boxFinset d (n + 1)).filter
            (fun y => (hypercubicLattice d).Adj b y))).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ psv_Bdry d n, (2 * d) := by
        apply Finset.sum_le_sum
        intro b _
        rw [Finset.card_product, Finset.card_singleton, one_mul]
        exact psv_nbr_card_le b _
    _ = (psv_Bdry d n).card * (2 * d) := by rw [Finset.sum_const, smul_eq_mul]




theorem psv_numerator_card_le (n : ℕ) :
    ((bondFinsetTouch d n \ bondFinsetInternal d n).card : ℕ)
      ≤ (psv_Bdry d n).card * (4 * d) := by
  
  have himg : bondFinsetTouch d n \ bondFinsetInternal d n
      ⊆ (bondPairsTouch d n \ bondPairsInternal d n).image (fun p => s(p.1, p.2)) := by
    intro e he
    rw [Finset.mem_sdiff] at he
    obtain ⟨hin, hout⟩ := he
    unfold bondFinsetTouch at hin
    rw [Finset.mem_image] at hin
    obtain ⟨p, hp, rfl⟩ := hin
    rw [Finset.mem_image]
    refine ⟨p, ?_, rfl⟩
    rw [Finset.mem_sdiff]
    refine ⟨hp, ?_⟩
    intro hpint
    exact hout (by unfold bondFinsetInternal; rw [Finset.mem_image]; exact ⟨p, hpint, rfl⟩)
  calc (bondFinsetTouch d n \ bondFinsetInternal d n).card
      ≤ ((bondPairsTouch d n \ bondPairsInternal d n).image (fun p => s(p.1, p.2))).card :=
        Finset.card_le_card himg
    _ ≤ (bondPairsTouch d n \ bondPairsInternal d n).card := Finset.card_image_le
    _ ≤ (((psv_Bdry d n) ×ˢ (boxFinset d (n + 1))).filter
          (fun q => (hypercubicLattice d).Adj q.1 q.2)).card * 2 := psv_ordered_diff_le n
    _ ≤ ((psv_Bdry d n).card * (2 * d)) * 2 :=
        Nat.mul_le_mul_right 2 (psv_filt_card_le n)
    _ = (psv_Bdry d n).card * (4 * d) := by ring





theorem psv_ratio_le (n : ℕ) (hd : 1 ≤ d) :
    ((bondFinsetTouch d n \ bondFinsetInternal d n).card : ℝ) / ((boxFinset d n).card : ℝ)
      ≤ (8 * (d : ℝ) ^ 2 * 3 ^ (d - 1)) / (2 * (n : ℝ) + 1) := by
  have hvol : ((boxFinset d n).card : ℝ) = (2 * (n : ℝ) + 1) ^ d := psv_volume_card_real d n
  have hvolpos : (0 : ℝ) < (2 * (n : ℝ) + 1) ^ d := by positivity
  have h2n1pos : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  
  have hnum : ((bondFinsetTouch d n \ bondFinsetInternal d n).card : ℝ)
      ≤ (4 * (d : ℝ)) * (2 * (d * (2 * (n : ℝ) + 3) ^ (d - 1))) := by
    calc ((bondFinsetTouch d n \ bondFinsetInternal d n).card : ℝ)
        ≤ (((psv_Bdry d n).card * (4 * d) : ℕ) : ℝ) := by exact_mod_cast psv_numerator_card_le n
      _ = (4 * (d : ℝ)) * ((psv_Bdry d n).card : ℝ) := by push_cast; ring
      _ ≤ (4 * (d : ℝ)) * (2 * (d * (2 * (n : ℝ) + 3) ^ (d - 1))) := by
          apply mul_le_mul_of_nonneg_left (psv_Bdry_card_real_le d n) (by positivity)
  
  have hpow : (2 * (n : ℝ) + 3) ^ (d - 1) ≤ 3 ^ (d - 1) * (2 * (n : ℝ) + 1) ^ (d - 1) := by
    rw [← mul_pow]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h1 : 2 * (n : ℝ) + 3 ≤ 3 * (2 * (n : ℝ) + 1) := by linarith
    gcongr
  
  have hnum2 : ((bondFinsetTouch d n \ bondFinsetInternal d n).card : ℝ)
      ≤ (8 * (d : ℝ) ^ 2 * 3 ^ (d - 1)) * (2 * (n : ℝ) + 1) ^ (d - 1) := by
    refine le_trans hnum ?_
    calc (4 * (d : ℝ)) * (2 * (d * (2 * (n : ℝ) + 3) ^ (d - 1)))
        = (8 * (d : ℝ) ^ 2) * (2 * (n : ℝ) + 3) ^ (d - 1) := by ring
      _ ≤ (8 * (d : ℝ) ^ 2) * (3 ^ (d - 1) * (2 * (n : ℝ) + 1) ^ (d - 1)) := by
          apply mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (8 * (d : ℝ) ^ 2 * 3 ^ (d - 1)) * (2 * (n : ℝ) + 1) ^ (d - 1) := by ring
  
  rw [hvol, div_le_div_iff₀ hvolpos h2n1pos]
  
  have hdsucc : d - 1 + 1 = d := by omega
  calc ((bondFinsetTouch d n \ bondFinsetInternal d n).card : ℝ) * (2 * (n : ℝ) + 1)
      ≤ ((8 * (d : ℝ) ^ 2 * 3 ^ (d - 1)) * (2 * (n : ℝ) + 1) ^ (d - 1)) * (2 * (n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hnum2 (by positivity)
    _ = (8 * (d : ℝ) ^ 2 * 3 ^ (d - 1)) * ((2 * (n : ℝ) + 1) ^ (d - 1) * (2 * (n : ℝ) + 1)) := by
        ring
    _ = (8 * (d : ℝ) ^ 2 * 3 ^ (d - 1)) * (2 * (n : ℝ) + 1) ^ d := by
        rw [← pow_succ, hdsucc]



theorem psv_ratio_card_tendsto_zero (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun n => ((bondFinsetTouch d n \ bondFinsetInternal d n).card : ℝ)
        / ((boxFinset d n).card : ℝ)) atTop (𝓝 0) := by
  set C : ℝ := 8 * (d : ℝ) ^ 2 * 3 ^ (d - 1) with hC
  have hbound : Tendsto (fun n : ℕ => C / (2 * (n : ℝ) + 1)) atTop (𝓝 0) := by
    have hden : Tendsto (fun n : ℕ => 2 * (n : ℝ) + 1) atTop atTop := by
      apply Filter.tendsto_atTop_add_const_right
      apply Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
      exact tendsto_natCast_atTop_atTop
    exact Tendsto.div_atTop tendsto_const_nhds hden
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) ?_ hbound
  exact Eventually.of_forall (fun n => psv_ratio_le n hd)





theorem psv_ratio_tendsto_zero (d : ℕ) (hd : 1 ≤ d) (β : ℝ) :
    Tendsto (fun n => (|β| * ((bondFinsetTouch d n \ bondFinsetInternal d n).card : ℝ))
        / ((boxFinset d n).card : ℝ)) atTop (𝓝 0) := by
  have h := (psv_ratio_card_tendsto_zero d hd).const_mul |β|
  rw [mul_zero] at h
  refine h.congr (fun n => ?_)
  rw [mul_div_assoc]













theorem psv_plus_free_pressure_indep {d : ℕ} (hd : 1 ≤ d) (β h : ℝ) :
    Tendsto (fun n =>
        Real.log (fvZ (plusField d) n (bondFinsetTouch d n) β h) / ((boxFinset d n).card : ℝ)
      - Real.log (fvZ (minusField d) n (bondFinsetInternal d n) β h)
          / ((boxFinset d n).card : ℝ))
      atTop (𝓝 0) :=
  plus_free_pressure_indep β h (psv_ratio_tendsto_zero d hd β)













theorem psv_boxPressure_full {d : ℕ} (hd : 1 ≤ d) (n : ℕ) (β h : ℝ) :
    ConvexOn ℝ Set.univ
        (fun β' : ℝ => Real.log (fvZ (plusField d) n (bondFinsetTouch d n) β' h))
      ∧ ConvexOn ℝ Set.univ
        (fun h' : ℝ => Real.log (fvZ (plusField d) n (bondFinsetTouch d n) β h'))
      ∧ Tendsto (fun m =>
            Real.log (fvZ (plusField d) m (bondFinsetTouch d m) β h)
              / ((boxFinset d m).card : ℝ)
          - Real.log (fvZ (minusField d) m (bondFinsetInternal d m) β h)
              / ((boxFinset d m).card : ℝ))
          atTop (𝓝 0) :=
  boxPressure_full n β h (psv_ratio_tendsto_zero d hd β)









theorem psv_boxPressure_plus_free_same_limit {d : ℕ} (hd : 1 ≤ d) (β h p : ℝ)
    (hplus : Tendsto
      (fun m => Real.log (fvZ (plusField d) m (bondFinsetTouch d m) β h)
        / ((boxFinset d m).card : ℝ)) atTop (𝓝 p)) :
    Tendsto
      (fun m => Real.log (fvZ (minusField d) m (bondFinsetInternal d m) β h)
        / ((boxFinset d m).card : ℝ)) atTop (𝓝 p) :=
  boxPressure_plus_free_same_limit β h p (psv_ratio_tendsto_zero d hd β) hplus

end Ising

end StatMech

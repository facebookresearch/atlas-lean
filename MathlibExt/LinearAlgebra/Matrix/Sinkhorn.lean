/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

open Matrix

namespace MathlibExt.LinearAlgebra.Matrix.SinkhornWanted

private noncomputable def sinkJ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (u : Fin n → ℝ) : ℝ :=
  ∑ i, Real.log (∑ j, A i j * Real.exp (u j)) - ∑ j, u j

private theorem sink_pos_min {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 < A i j) (ne : Nonempty (Fin n)) :
    ∃ m : ℝ, 0 < m ∧ ∀ i j, m ≤ A i j := by
  classical
  let s : Finset ℝ := Finset.univ.image (fun p : Fin n × Fin n => A p.1 p.2)
  have hne : Nonempty (Fin n × Fin n) :=
    ⟨(Classical.choice ne, Classical.choice ne)⟩
  have hs : s.Nonempty :=
    Finset.image_nonempty.mpr (Finset.univ_nonempty_iff.mpr hne)
  refine ⟨s.min' hs, ?_, ?_⟩
  · obtain ⟨p, _, hp⟩ := Finset.mem_image.mp (Finset.min'_mem s hs)
    rw [← hp]
    exact hA p.1 p.2
  · intro i j
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩

private theorem sinkJ_cont {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 < A i j) (ne : Nonempty (Fin n)) :
    Continuous (sinkJ A) := by
  unfold sinkJ
  apply Continuous.sub
  · apply continuous_finsetSum Finset.univ (fun i _ => ?_)
    apply Continuous.log
    · apply continuous_finsetSum Finset.univ (fun j _ => ?_)
      exact continuous_const.mul
        (Real.continuous_exp.comp (continuous_apply j))
    · intro u
      apply ne_of_gt
      apply Finset.sum_pos (fun j _ => mul_pos (hA _ _) (Real.exp_pos _))
      exact Finset.univ_nonempty_iff.mpr ne
  · exact continuous_finsetSum Finset.univ (fun j _ => continuous_apply j)

private theorem sinkJ_row_lb {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 < A i j) (m : ℝ) (hm : 0 < m) (hmA : ∀ i j, m ≤ A i j)
    (u : Fin n → ℝ) (M : ℝ) (j₀ : Fin n) (hM : u j₀ = M) (i : Fin n) :
    Real.log m + M ≤ Real.log (∑ j, A i j * Real.exp (u j)) := by
  have e : Real.exp (u j₀) = Real.exp M := by rw [hM]
  have h1 : m * Real.exp M ≤ ∑ j, A i j * Real.exp (u j) := by
    calc m * Real.exp M ≤ A i j₀ * Real.exp (u j₀) := by
            rw [e]
            exact mul_le_mul (hmA i j₀) le_rfl (le_of_lt (Real.exp_pos _))
              (le_of_lt (hA i j₀))
      _ ≤ _ := Finset.single_le_sum
          (fun j _ => mul_nonneg (le_of_lt (hA i j)) (le_of_lt (Real.exp_pos _)))
          (Finset.mem_univ j₀)
  have hpos : (0 : ℝ) < m * Real.exp M := mul_pos hm (Real.exp_pos M)
  calc Real.log m + M = Real.log (m * Real.exp M) := by
          rw [Real.log_mul (ne_of_gt hm) (ne_of_gt (Real.exp_pos M)), Real.log_exp]
    _ ≤ _ := Real.log_le_log hpos h1

private theorem sinkJ_lower {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (m : ℝ) (u : Fin n → ℝ) (M : ℝ) (hsum : ∑ i, u i = 0)
    (hlb : ∀ i, Real.log m + M ≤ Real.log (∑ j, A i j * Real.exp (u j))) :
    (n : ℝ) * Real.log m + (n : ℝ) * M ≤ sinkJ A u := by
  unfold sinkJ
  rw [hsum, sub_zero]
  have h2 : ∑ _i : Fin n, (Real.log m + M)
      ≤ ∑ i, Real.log (∑ j, A i j * Real.exp (u j)) :=
    Finset.sum_le_sum (fun i _ => hlb i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
  linarith [h2]

private theorem sink_abs_sum {n : ℕ} (u : Fin n → ℝ) (hsum : ∑ i, u i = 0) :
    ∑ i, |u i|
      = 2 * (∑ i ∈ Finset.univ.filter (fun i => 0 < u i), u i) := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => 0 < u i)
    (fun i => u i)
  have hneg : ∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < u i), u i
      = -(∑ i ∈ Finset.univ.filter (fun i => 0 < u i), u i) := by
    have h0 : (∑ i ∈ Finset.univ.filter (fun i => 0 < u i), u i)
        + ∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < u i), u i = 0 := by
      rw [hsplit]; exact hsum
    linarith [h0]
  have hs2 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => 0 < u i)
    (fun i => |u i|)
  have e1 : ∑ i ∈ Finset.univ.filter (fun i => 0 < u i), |u i|
      = ∑ i ∈ Finset.univ.filter (fun i => 0 < u i), u i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_filter] at hi
    exact abs_of_pos hi.2
  have e2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < u i), |u i|
      = ∑ i ∈ Finset.univ.filter (fun i => 0 < u i), u i := by
    have e3 : ∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < u i), |u i|
        = ∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < u i), -(u i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_filter] at hi
      exact abs_of_nonpos (le_of_not_gt hi.2)
    rw [e3, Finset.sum_neg_distrib, hneg]
    ring
  linarith [hs2, e1, e2]

private theorem sink_max_sq {n : ℕ} (hn : 0 < n)
    (u : Fin n → ℝ) (M : ℝ) (hsum : ∑ i, u i = 0) (hle : ∀ i, u i ≤ M) :
    0 ≤ M ∧ ∑ i, u i ^ 2 ≤ 4 * (n : ℝ) ^ 2 * M ^ 2 := by
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hM0 : 0 ≤ M := by
    by_contra hcon
    have hlt : M < 0 := lt_of_not_ge hcon
    have hle2 : ∑ i, u i ≤ Fintype.card (Fin n) • M :=
      Finset.sum_le_card_nsmul _ _ _ (fun i _ => hle i)
    rw [Fintype.card_fin, nsmul_eq_mul, hsum] at hle2
    nlinarith [hle2, hN, hlt]
  refine ⟨hM0, ?_⟩
  classical
  have hPle : (∑ i ∈ Finset.univ.filter (fun i => 0 < u i), u i) ≤ (n : ℝ) * M := by
    calc (∑ i ∈ Finset.univ.filter (fun i => 0 < u i), u i)
          ≤ (Finset.univ.filter (fun i => 0 < u i)).card • M :=
          Finset.sum_le_card_nsmul _ _ _ (fun i _ => hle i)
      _ ≤ (n : ℝ) * M := by
          rw [nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ hM0
          calc ((Finset.univ.filter (fun i => 0 < u i)).card : ℝ)
                ≤ ((Finset.univ).card : ℝ) :=
                Nat.cast_le.mpr (Finset.card_filter_le _ _)
            _ = (n : ℝ) := by rw [Finset.card_univ, Fintype.card_fin]
  have habs := sink_abs_sum u hsum
  have hbound : ∀ i, |u i| ≤ 2 * (n : ℝ) * M := by
    intro i
    calc |u i| ≤ ∑ k, |u k| := Finset.single_le_sum
            (fun k _ => abs_nonneg (u k)) (Finset.mem_univ i)
      _ = 2 * (∑ i ∈ Finset.univ.filter (fun i => 0 < u i), u i) := habs
      _ ≤ 2 * (n : ℝ) * M := by linarith [hPle]
  have hsq : ∀ i, u i ^ 2 ≤ |u i| * (2 * (n : ℝ) * M) := by
    intro i
    calc u i ^ 2 = |u i| * |u i| := by rw [← sq_abs]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbound i) (abs_nonneg _)
  have hnn : (0 : ℝ) ≤ 2 * (n : ℝ) * M := by
    have hcc : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hN
    positivity
  have h2P : 2 * (∑ i ∈ Finset.univ.filter (fun i => 0 < u i), u i)
      ≤ 2 * (n : ℝ) * M := by linarith [hPle]
  calc ∑ i, u i ^ 2 ≤ ∑ i, |u i| * (2 * (n : ℝ) * M) :=
          Finset.sum_le_sum (fun i _ => hsq i)
    _ = (∑ i, |u i|) * (2 * (n : ℝ) * M) := (Finset.sum_mul ..).symm
    _ = 2 * (∑ i ∈ Finset.univ.filter (fun i => 0 < u i), u i)
        * (2 * (n : ℝ) * M) := by rw [habs]
    _ ≤ 4 * (n : ℝ) ^ 2 * M ^ 2 := by
          have hmul := mul_le_mul h2P le_rfl hnn hnn
          nlinarith [hmul]

private theorem sinkJ_large {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 < A i j) (m : ℝ) (hm : 0 < m) (hmA : ∀ i j, m ≤ A i j)
    (u : Fin n → ℝ) (hsum : ∑ i, u i = 0)
    (hbig : (2 * max (sinkJ A 0 - (n : ℝ) * Real.log m) 0 + 1) ^ 2
      < ∑ i, u i ^ 2) :
    sinkJ A 0 < sinkJ A u := by
  classical
  set R := (2 * max (sinkJ A 0 - (n : ℝ) * Real.log m) 0 + 1) with hRdef
  obtain ⟨j₀, _, hj₀⟩ := Finset.exists_max_image Finset.univ u
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
  have hle : ∀ i, u i ≤ u j₀ := fun i => hj₀ i (Finset.mem_univ i)
  have hsq := (sink_max_sq hn u (u j₀) hsum hle).2
  have hM0 := (sink_max_sq hn u (u j₀) hsum hle).1
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h2nMnn : (0 : ℝ) ≤ 2 * (n : ℝ) * (u j₀) + R := by
    have hcc : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hN
    rw [hRdef]
    positivity
  have hpos : (0 : ℝ) < 4 * (n : ℝ) ^ 2 * (u j₀) ^ 2 - R ^ 2 := by
    linarith [hbig, hsq]
  have hfac : 4 * (n : ℝ) ^ 2 * (u j₀) ^ 2 - R ^ 2
      = (2 * (n : ℝ) * (u j₀) + R) * (2 * (n : ℝ) * (u j₀) - R) := by ring
  have hgt : (0 : ℝ) < 2 * (n : ℝ) * (u j₀) - R := by
    by_contra hcon
    have hle' : 2 * (n : ℝ) * (u j₀) - R ≤ 0 := le_of_not_gt hcon
    have hnp := mul_nonpos_of_nonpos_of_nonneg hle' h2nMnn
    nlinarith [hpos, hfac, hnp]
  have hnM : R / 2 < (n : ℝ) * (u j₀) := by linarith [hgt]
  rw [hRdef] at hnM
  have hlb := sinkJ_lower A m u (u j₀) hsum
    (fun i => sinkJ_row_lb A hA m hm hmA u (u j₀) j₀ rfl i)
  have hmax : sinkJ A 0 - (n : ℝ) * Real.log m
      ≤ max (sinkJ A 0 - (n : ℝ) * Real.log m) 0 := le_max_left _ _
  linarith [hlb, hnM, hmax]

private theorem sinkJ_exists_min {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j)
    (ne : Nonempty (Fin n)) (m : ℝ) :
    ∃ u_star : Fin n → ℝ, (∑ i, u_star i = 0) ∧
      (∑ i, u_star i ^ 2
        ≤ (2 * max (sinkJ A 0 - (n : ℝ) * Real.log m) 0 + 1) ^ 2 + 1) ∧
      ∀ v : Fin n → ℝ, (∑ i, v i = 0) →
        (∑ i, v i ^ 2
          ≤ (2 * max (sinkJ A 0 - (n : ℝ) * Real.log m) 0 + 1) ^ 2 + 1) →
        sinkJ A u_star ≤ sinkJ A v := by
  classical
  set R := (2 * max (sinkJ A 0 - (n : ℝ) * Real.log m) 0 + 1) with hRdef
  have hclosed1 : IsClosed {u : Fin n → ℝ | ∑ i, u i = 0} :=
    isClosed_eq (continuous_finsetSum _ (fun i _ => continuous_apply i))
      continuous_const
  have hcont2 : Continuous (fun u : Fin n → ℝ => ∑ i, u i ^ 2) := by
    apply continuous_finsetSum _ (fun i _ => ?_)
    exact ((continuous_apply i : Continuous (fun u : Fin n → ℝ => u i)).pow 2)
  have hclosed2 : IsClosed {u : Fin n → ℝ | ∑ i, u i ^ 2 ≤ R ^ 2 + 1} :=
    isClosed_le hcont2 continuous_const
  have hsub : {u : Fin n → ℝ | ∑ i, u i = 0} ∩ {u | ∑ i, u i ^ 2 ≤ R ^ 2 + 1}
      ⊆ Metric.closedBall 0 (R ^ 2 + 2) := by
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [pi_norm_le_iff_of_nonempty u]
    intro b
    rw [Real.norm_eq_abs]
    have hsq1 : (u b) ^ 2 ≤ R ^ 2 + 1 :=
      le_trans (Finset.single_le_sum (fun k _ => sq_nonneg (u k))
        (Finset.mem_univ b)) hu.2
    calc |u b| = Real.sqrt ((u b) ^ 2) := by rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt ((R ^ 2 + 2) ^ 2) := by
          apply Real.sqrt_le_sqrt
          nlinarith [hsq1, sq_nonneg (R ^ 2)]
      _ = R ^ 2 + 2 := by
          apply Real.sqrt_sq
          positivity
  have hcompact : IsCompact
      ({u : Fin n → ℝ | ∑ i, u i = 0} ∩ {u | ∑ i, u i ^ 2 ≤ R ^ 2 + 1}) :=
    IsCompact.of_isClosed_subset (isCompact_closedBall 0 (R ^ 2 + 2))
      (hclosed1.inter hclosed2) hsub
  have hne : ({u : Fin n → ℝ | ∑ i, u i = 0}
      ∩ {u | ∑ i, u i ^ 2 ≤ R ^ 2 + 1}).Nonempty := by
    refine ⟨0, ?_, ?_⟩
    · show (∑ i, ((0 : Fin n → ℝ) i)) = 0
      simp
    · show (∑ i, ((0 : Fin n → ℝ) i) ^ 2) ≤ R ^ 2 + 1
      calc (∑ i, ((0 : Fin n → ℝ) i) ^ 2) = 0 := by simp
        _ ≤ R ^ 2 + 1 := by positivity
  obtain ⟨u_star, hmem, hmin⟩ :=
    hcompact.exists_isMinOn hne (sinkJ_cont A hA ne).continuousOn
  exact ⟨u_star, hmem.1, hmem.2, fun v hv1 hv2 => hmin ⟨hv1, hv2⟩⟩

private theorem hasDerivAt_piadd {f g : ℝ → ℝ} {f' g' : ℝ} {x : ℝ}
    (h : HasDerivAt (f + g) (f' + g') x) :
    HasDerivAt (fun t => f t + g t) (f' + g') x := by
  have hfun : (f + g) = (fun t => f t + g t) := by
    funext t
    exact (Pi.add_apply f g t).symm
  rwa [hfun] at h

private theorem hasDerivAt_pisub {f g : ℝ → ℝ} {f' g' : ℝ} {x : ℝ}
    (h : HasDerivAt (f - g) (f' - g') x) :
    HasDerivAt (fun t => f t - g t) (f' - g') x := by
  have hfun : (f - g) = (fun t => f t - g t) := by
    funext t
    exact (Pi.sub_apply f g t).symm
  rwa [hfun] at h

private theorem hasDerivAt_pisum {n : ℕ} {s : Finset (Fin n)} {F : Fin n → ℝ → ℝ}
    {F' : Fin n → ℝ} {x : ℝ}
    (h : HasDerivAt (∑ j ∈ s, F j) (∑ j ∈ s, F' j) x) :
    HasDerivAt (fun t => ∑ j ∈ s, F j t) (∑ j ∈ s, F' j) x := by
  have hfun : (∑ j ∈ s, F j) = (fun t => ∑ j ∈ s, F j t) := by
    funext t
    exact Finset.sum_apply t s F
  rwa [hfun] at h

private theorem sinkJ_crit {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 < A i j)
    (c : Fin n → ℝ) (k l : Fin n)
    (hg : ∀ t : ℝ, sinkJ A c
      ≤ sinkJ A (fun j => c j
        + t * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0)))) :
    Real.exp (c k) * (∑ i, A i k / (∑ j, A i j * Real.exp (c j)))
      = Real.exp (c l) * (∑ i, A i l / (∑ j, A i j * Real.exp (c j))) := by
  classical
  have hpos : ∀ i, (0 : ℝ) < ∑ j, A i j * Real.exp (c j) :=
    fun i => Finset.sum_pos (fun j _ => mul_pos (hA i j) (Real.exp_pos _))
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
  have hbase : ∀ j, HasDerivAt
      (fun t : ℝ => c j
        + t * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0)))
      ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0)) 0 := by
    intro j
    have h1 : HasDerivAt
        (fun t : ℝ => t
          * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0)))
        ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0)) 0 := by
      have h := (hasDerivAt_id (0 : ℝ)).mul_const
        ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0))
      simpa using h
    have h2 := hasDerivAt_piadd ((hasDerivAt_const (0 : ℝ) (c j)).add h1)
    simpa using h2
  have hexp : ∀ j, HasDerivAt
      (fun t : ℝ => Real.exp (c j
        + t * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0))))
      (Real.exp (c j)
        * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0))) 0 := by
    intro j
    have h := (hbase j).exp
    simp only [zero_mul, add_zero] at h
    exact h
  have hterm : ∀ i j, HasDerivAt
      (fun t : ℝ => A i j * Real.exp (c j
        + t * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0))))
      (A i j * (Real.exp (c j)
        * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0)))) 0 :=
    fun i j => HasDerivAt.const_mul (A i j) (hexp j)
  have hsumN : ∀ i, HasDerivAt
      (fun t : ℝ => ∑ j, A i j * Real.exp (c j
        + t * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0))))
      (∑ j, A i j * (Real.exp (c j)
        * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0)))) 0 :=
    fun i => hasDerivAt_pisum (HasDerivAt.sum (fun j _ => hterm i j))
  have hlog : ∀ i, HasDerivAt
      (fun t : ℝ => Real.log (∑ j, A i j * Real.exp (c j
        + t * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0)))))
      ((∑ j, A i j * (Real.exp (c j)
        * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0))))
        / (∑ j, A i j * Real.exp (c j))) 0 := by
    intro i
    have hx : ∀ j, c j
        + (0 : ℝ) * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0))
        = c j := by
      intro j
      simp only [zero_mul, add_zero]
    have hne : (∑ j, A i j * Real.exp (c j
        + (0 : ℝ) * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0))))
        ≠ 0 := by
      have heq : (∑ j, A i j * Real.exp (c j
          + (0 : ℝ) * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0))))
          = ∑ j, A i j * Real.exp (c j) :=
        Finset.sum_congr rfl (fun j _ => by rw [hx j])
      rw [heq]
      exact ne_of_gt (hpos i)
    have h := (hsumN i).log hne
    simp only [zero_mul, add_zero] at h
    exact h
  have hlogsum : HasDerivAt
      (fun t : ℝ => ∑ i, Real.log (∑ j, A i j * Real.exp (c j
        + t * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0)))))
      (∑ i, (∑ j, A i j * (Real.exp (c j)
        * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0))))
        / (∑ j, A i j * Real.exp (c j))) 0 :=
    hasDerivAt_pisum (HasDerivAt.sum (fun i _ => hlog i))
  have hwsum : HasDerivAt
      (fun t : ℝ => ∑ j, (c j
        + t * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0))))
      (0 : ℝ) 0 := by
    have h1 : HasDerivAt
        (fun t : ℝ => ∑ j, (c j
          + t * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0))))
        (∑ j, ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0))) 0 :=
      hasDerivAt_pisum (HasDerivAt.sum (fun j _ => hbase j))
    have h2 : (∑ j, ((if j = k then (1 : ℝ) else 0)
        - (if j = l then (1 : ℝ) else 0))) = 0 := by
      rw [Finset.sum_sub_distrib]
      have e1 : (∑ j, (if j = k then (1 : ℝ) else 0)) = 1 := by
        rw [Finset.sum_ite_eq']
        simp
      have e2 : (∑ j, (if j = l then (1 : ℝ) else 0)) = 1 := by
        rw [Finset.sum_ite_eq']
        simp
      rw [e1, e2, sub_self]
    rw [h2] at h1
    exact h1
  have hD : (∑ i, (∑ j, A i j * (Real.exp (c j)
        * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0))))
        / (∑ j, A i j * Real.exp (c j)))
      = Real.exp (c k) * (∑ i, A i k / (∑ j, A i j * Real.exp (c j)))
        - Real.exp (c l) * (∑ i, A i l / (∑ j, A i j * Real.exp (c j))) := by
    have per : ∀ i, (∑ j, A i j * (Real.exp (c j)
        * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0))))
        = A i k * Real.exp (c k) - A i l * Real.exp (c l) := by
      intro i
      have e0 : ∀ j, A i j * (Real.exp (c j)
          * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0)))
          = (A i j * Real.exp (c j) * (if j = k then (1 : ℝ) else 0))
            - (A i j * Real.exp (c j) * (if j = l then (1 : ℝ) else 0)) := by
        intro j
        ring
      rw [Finset.sum_congr rfl (fun j _ => e0 j), Finset.sum_sub_distrib]
      congr 1
      · have e1 : ∀ j, A i j * Real.exp (c j) * (if j = k then (1 : ℝ) else 0)
            = (if j = k then A i j * Real.exp (c j) else 0) := by
          intro j
          by_cases h : j = k <;> simp [h]
        rw [Finset.sum_congr rfl (fun j _ => e1 j), Finset.sum_ite_eq']
        simp
      · have e2 : ∀ j, A i j * Real.exp (c j) * (if j = l then (1 : ℝ) else 0)
            = (if j = l then A i j * Real.exp (c j) else 0) := by
          intro j
          by_cases h : j = l <;> simp [h]
        rw [Finset.sum_congr rfl (fun j _ => e2 j), Finset.sum_ite_eq']
        simp
    calc (∑ i, (∑ j, A i j * (Real.exp (c j)
          * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0))))
          / (∑ j, A i j * Real.exp (c j)))
        = ∑ i, ((A i k * Real.exp (c k) - A i l * Real.exp (c l))
          / (∑ j, A i j * Real.exp (c j))) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [per i]
      _ = (∑ i, (A i k * Real.exp (c k)) / (∑ j, A i j * Real.exp (c j)))
          - (∑ i, (A i l * Real.exp (c l)) / (∑ j, A i j * Real.exp (c j))) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [sub_div]
      _ = _ := by
          rw [show (∑ i, (A i k * Real.exp (c k)) / (∑ j, A i j * Real.exp (c j)))
              = Real.exp (c k) * (∑ i, A i k / (∑ j, A i j * Real.exp (c j))) from by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring]
          rw [show (∑ i, (A i l * Real.exp (c l)) / (∑ j, A i j * Real.exp (c j)))
              = Real.exp (c l) * (∑ i, A i l / (∑ j, A i j * Real.exp (c j))) from by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring]
  have hderiv : HasDerivAt
      (fun t : ℝ => (∑ i, Real.log (∑ j, A i j * Real.exp (c j
        + t * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0)))))
        - (∑ j, (c j
          + t * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0)))))
      (Real.exp (c k) * (∑ i, A i k / (∑ j, A i j * Real.exp (c j)))
        - Real.exp (c l) * (∑ i, A i l / (∑ j, A i j * Real.exp (c j)))) 0 := by
    have h := hasDerivAt_pisub (hlogsum.sub hwsum)
    rw [hD] at h
    simpa using h
  have hmin : IsMinOn
      (fun t : ℝ => sinkJ A (fun j => c j
        + t * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0))))
      Set.univ 0 := by
    rw [isMinOn_univ_iff]
    intro t
    show sinkJ A (fun j => c j
        + (0 : ℝ) * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0)))
      ≤ sinkJ A (fun j => c j
        + t * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0)))
    have e0 : (fun j => c j
        + (0 : ℝ) * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0)))
        = c := by
      funext j
      simp only [zero_mul, add_zero]
    rw [e0]
    exact hg t
  have hloc := hmin.isLocalMin Filter.univ_mem
  have hzero := hloc.hasDerivAt_eq_zero hderiv
  linarith [hzero]

/--
**Sinkhorn's scaling theorem.** Let $n \ge 1$ and let $A$ be a real $n \times n$ matrix all of
whose entries are strictly positive. Then there are vectors $r, c \in \mathbb{R}^n$ with strictly
positive entries such that the matrix with entries $r_i A_{ij} c_j$ is doubly stochastic, that is,
its entries are nonnegative and each of its rows and each of its columns sums to $1$.

Source: R. Sinkhorn, Ann. Math. Statist. 35 (1964), 876-879, DOI 10.1214/aoms/1177703591.
Proves `Wanted` entry `sinkhorn_scaling`.
-/
theorem sinkhorn_scaling {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 < A i j) :
    ∃ (r c : Fin n → ℝ), (∀ i, 0 < r i) ∧ (∀ j, 0 < c j) ∧
      (fun i j => r i * A i j * c j) ∈ doublyStochastic ℝ (Fin n) := by
  classical
  have ne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨m, hm, hmA⟩ := sink_pos_min A hA ne
  obtain ⟨u, hsum, hball, hmin⟩ := sinkJ_exists_min A hA ne m
  have hS : ∀ i, (0 : ℝ) < ∑ j, A i j * Real.exp (u j) :=
    fun i => Finset.sum_pos (fun j _ => mul_pos (hA i j) (Real.exp_pos _))
      (Finset.univ_nonempty_iff.mpr ne)
  have e1 : ∀ a : Fin n, (∑ j, (if j = a then (1 : ℝ) else 0)) = 1 := by
    intro a
    rw [Finset.sum_ite_eq']
    simp
  have hsec : ∀ (k l : Fin n) (t : ℝ),
      ∑ j, (u j
        + t * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0)))
        = 0 := by
    intro k l t
    have e : (∑ j, (u j
        + t * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0))))
        = (∑ j, u j)
          + t * ((∑ j, (if j = k then (1 : ℝ) else 0))
            - (∑ j, (if j = l then (1 : ℝ) else 0))) := by
      rw [Finset.sum_add_distrib]
      congr 1
      calc (∑ j, t * ((if j = k then (1 : ℝ) else 0)
          - (if j = l then (1 : ℝ) else 0)))
          = (∑ j, t * (if j = k then (1 : ℝ) else 0))
            - (∑ j, t * (if j = l then (1 : ℝ) else 0)) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            ring
        _ = t * ((∑ j, (if j = k then (1 : ℝ) else 0))
            - (∑ j, (if j = l then (1 : ℝ) else 0))) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum, mul_sub]
    rw [e, hsum, e1 k, e1 l]
    ring
  have hgline : ∀ (k l : Fin n) (t : ℝ), sinkJ A u
      ≤ sinkJ A (fun j => u j
        + t * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0))) := by
    intro k l t
    by_cases ht : ∑ j, ((u j
        + t * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0))) ^ 2)
        ≤ (2 * max (sinkJ A 0 - (n : ℝ) * Real.log m) 0 + 1) ^ 2 + 1
    · exact hmin _ (hsec k l t) ht
    · have hout : (2 * max (sinkJ A 0 - (n : ℝ) * Real.log m) 0 + 1) ^ 2 + 1
          ≤ ∑ j, ((u j
            + t * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0))) ^ 2) :=
          le_of_not_ge ht
      have hbig : (2 * max (sinkJ A 0 - (n : ℝ) * Real.log m) 0 + 1) ^ 2
          < ∑ j, ((u j
            + t * ((if j = k then (1 : ℝ) else 0) - (if j = l then (1 : ℝ) else 0))) ^ 2) := by
        linarith [hout]
      have hlt := sinkJ_large hn A hA m hm hmA _ (hsec k l t) hbig
      have h0sum : (∑ j, ((0 : Fin n → ℝ) j)) = 0 := by simp
      have h0ball : (∑ j, ((0 : Fin n → ℝ) j) ^ 2)
          ≤ (2 * max (sinkJ A 0 - (n : ℝ) * Real.log m) 0 + 1) ^ 2 + 1 := by
        calc (∑ j, ((0 : Fin n → ℝ) j) ^ 2) = 0 := by simp
          _ ≤ _ := by positivity
      have h0 : sinkJ A u ≤ sinkJ A 0 := hmin 0 h0sum h0ball
      linarith [hlt, h0]
  have hQeq : ∀ k l : Fin n, Real.exp (u k)
      * (∑ i, A i k / (∑ j, A i j * Real.exp (u j)))
      = Real.exp (u l) * (∑ i, A i l / (∑ j, A i j * Real.exp (u j))) :=
    fun k l => sinkJ_crit hn A hA u k l (hgline k l)
  have hQsum : (∑ k, Real.exp (u k) * (∑ i, A i k / (∑ j, A i j * Real.exp (u j))))
      = (n : ℝ) := by
    have step1 : ∀ k : Fin n, Real.exp (u k) * (∑ i, A i k / (∑ j, A i j * Real.exp (u j)))
        = ∑ i, (A i k * Real.exp (u k)) / (∑ j, A i j * Real.exp (u j)) := by
      intro k
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    calc (∑ k, Real.exp (u k) * (∑ i, A i k / (∑ j, A i j * Real.exp (u j))))
        = ∑ k, ∑ i, (A i k * Real.exp (u k)) / (∑ j, A i j * Real.exp (u j)) :=
          Finset.sum_congr rfl (fun k _ => step1 k)
      _ = ∑ i, ∑ k, (A i k * Real.exp (u k)) / (∑ j, A i j * Real.exp (u j)) :=
          Finset.sum_comm
      _ = ∑ i, (∑ k, A i k * Real.exp (u k)) / (∑ j, A i j * Real.exp (u j)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_div]
      _ = ∑ _i : Fin n, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro i _
          exact div_self (ne_of_gt (hS i))
      _ = (n : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            mul_one]
  obtain ⟨k₀⟩ := ne
  have hQ1 : ∀ k : Fin n, Real.exp (u k)
      * (∑ i, A i k / (∑ j, A i j * Real.exp (u j))) = 1 := by
    have hconst : ∀ k : Fin n, Real.exp (u k)
        * (∑ i, A i k / (∑ j, A i j * Real.exp (u j)))
        = Real.exp (u k₀) * (∑ i, A i k₀ / (∑ j, A i j * Real.exp (u j))) :=
      fun k => hQeq k k₀
    have hsum2 : (∑ k, Real.exp (u k) * (∑ i, A i k / (∑ j, A i j * Real.exp (u j))))
        = (n : ℝ) * (Real.exp (u k₀)
          * (∑ i, A i k₀ / (∑ j, A i j * Real.exp (u j)))) := by
      calc (∑ k, Real.exp (u k) * (∑ i, A i k / (∑ j, A i j * Real.exp (u j))))
          = ∑ _k : Fin n, Real.exp (u k₀)
            * (∑ i, A i k₀ / (∑ j, A i j * Real.exp (u j))) :=
            Finset.sum_congr rfl (fun k _ => hconst k)
        _ = _ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hN0 : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
    have hQk0 : Real.exp (u k₀) * (∑ i, A i k₀ / (∑ j, A i j * Real.exp (u j)))
        = 1 := by
      have hnn : (n : ℝ)
          * (Real.exp (u k₀) * (∑ i, A i k₀ / (∑ j, A i j * Real.exp (u j))))
          = (n : ℝ) * 1 := by
        rw [mul_one]
        linarith [hsum2, hQsum]
      exact mul_left_cancel₀ hN0 hnn
    intro k
    rw [hconst k, hQk0]
  refine ⟨fun i => (∑ j, A i j * Real.exp (u j))⁻¹, fun j => Real.exp (u j),
    ?_, ?_, ?_⟩
  · intro i
    exact inv_pos.mpr (hS i)
  · intro j
    exact Real.exp_pos _
  · refine mem_doublyStochastic_iff_sum.mpr ⟨?_, ?_, ?_⟩
    · intro i j
      show (0 : ℝ)
        ≤ (∑ j', A i j' * Real.exp (u j'))⁻¹ * A i j * Real.exp (u j)
      exact mul_nonneg
        (mul_nonneg (le_of_lt (inv_pos.mpr (hS i))) (le_of_lt (hA i j)))
        (le_of_lt (Real.exp_pos _))
    · intro i
      show (∑ j, (∑ j', A i j' * Real.exp (u j'))⁻¹ * A i j * Real.exp (u j))
        = 1
      calc (∑ j, (∑ j', A i j' * Real.exp (u j'))⁻¹ * A i j * Real.exp (u j))
          = ∑ j, (∑ j', A i j' * Real.exp (u j'))⁻¹
            * (A i j * Real.exp (u j)) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
        _ = (∑ j', A i j' * Real.exp (u j'))⁻¹
            * (∑ j, A i j * Real.exp (u j)) := by
            rw [Finset.mul_sum]
        _ = 1 := inv_mul_cancel₀ (ne_of_gt (hS i))
    · intro k
      show (∑ i, (∑ j', A i j' * Real.exp (u j'))⁻¹ * A i k * Real.exp (u k))
        = 1
      have hcol : (∑ i, (∑ j', A i j' * Real.exp (u j'))⁻¹ * A i k
          * Real.exp (u k))
          = Real.exp (u k) * (∑ i, A i k / (∑ j', A i j' * Real.exp (u j'))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hcol]
      exact hQ1 k

end MathlibExt.LinearAlgebra.Matrix.SinkhornWanted

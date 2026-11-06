/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open Finset
open scoped InnerProductSpace

-- N1: weighted variance identity
private theorem kirszbraun_sum_mul_mul_norm_sub_sq_eq
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (u : ι → G) (z : G)
    (hsum : ∑ i ∈ s, a i = 1) :
    ∑ i ∈ s, ∑ j ∈ s, a i * a j * ‖u i - u j‖ ^ 2
      = 2 * ∑ i ∈ s, a i * ‖u i - z‖ ^ 2 - 2 * ‖∑ i ∈ s, a i • u i - z‖ ^ 2 := by
  set v : ι → G := fun i => u i - z with hv
  have hvv : ∀ i j, u i - u j = v i - v j := fun i j => by
    simp [hv, sub_sub_sub_cancel_right]
  have hsumv : ∑ i ∈ s, a i • v i = (∑ i ∈ s, a i • u i) - z := by
    simp only [hv, smul_sub, Finset.sum_sub_distrib]
    congr 1
    rw [← Finset.sum_smul]
    simp [hsum]
  have hexpand : ∀ i j : ι, ‖v i - v j‖ ^ 2
      = ‖v i‖ ^ 2 - 2 * ⟪v i, v j⟫_ℝ + ‖v j‖ ^ 2 := fun i j => by
    have h := norm_sub_sq_real (v i) (v j)
    linarith [h]
  calc ∑ i ∈ s, ∑ j ∈ s, a i * a j * ‖u i - u j‖ ^ 2
      = ∑ i ∈ s, ∑ j ∈ s, a i * a j * ‖v i - v j‖ ^ 2 := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [hvv]
    _ = ∑ i ∈ s, ∑ j ∈ s, (a i * a j * ‖v i‖ ^ 2 - a i * a j * (2 * ⟪v i, v j⟫_ℝ) + a i * a j * ‖v
        j‖ ^ 2) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [hexpand]; ring
    _ = (∑ i ∈ s, ∑ j ∈ s, a i * a j * ‖v i‖ ^ 2)
        - (∑ i ∈ s, ∑ j ∈ s, a i * a j * (2 * ⟪v i, v j⟫_ℝ))
        + (∑ i ∈ s, ∑ j ∈ s, a i * a j * ‖v j‖ ^ 2) := by
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = 2 * ∑ i ∈ s, a i * ‖v i‖ ^ 2 - 2 * ‖∑ i ∈ s, a i • v i‖ ^ 2 := by
        have h1 : ∑ i ∈ s, ∑ j ∈ s, a i * a j * ‖v i‖ ^ 2 = ∑ i ∈ s, a i * ‖v i‖ ^ 2 := by
          apply Finset.sum_congr rfl; intro i hi
          have hmul : (∑ j ∈ s, a i * a j * ‖v i‖ ^ 2) = a i * ‖v i‖ ^ 2 * (∑ j ∈ s, a j) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; ring
          rw [hmul, hsum, mul_one]
        have h2 : ∑ i ∈ s, ∑ j ∈ s, a i * a j * ‖v j‖ ^ 2 = ∑ i ∈ s, a i * ‖v i‖ ^ 2 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro j hj
          have hmul : (∑ i ∈ s, a i * a j * ‖v j‖ ^ 2) = a j * ‖v j‖ ^ 2 * (∑ i ∈ s, a i) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring
          rw [hmul, hsum, mul_one]
        have hcross : ∑ i ∈ s, ∑ j ∈ s, a i * a j * (2 * ⟪v i, v j⟫_ℝ)
            = 2 * ‖∑ i ∈ s, a i • v i‖ ^ 2 := by
          have hinner : ∑ i ∈ s, ∑ j ∈ s, a i * a j * ⟪v i, v j⟫_ℝ
              = ⟪∑ i ∈ s, a i • v i, ∑ j ∈ s, a j • v j⟫_ℝ := by
            rw [sum_inner]
            apply Finset.sum_congr rfl; intro i hi
            rw [inner_sum]
            apply Finset.sum_congr rfl; intro j hj
            rw [real_inner_smul_left, real_inner_smul_right]; ring
          have hnorm : ⟪∑ i ∈ s, a i • v i, ∑ j ∈ s, a j • v j⟫_ℝ = ‖∑ i ∈ s, a i • v i‖ ^ 2 := by
            rw [real_inner_self_eq_norm_sq]
          have hscale : ∑ i ∈ s, ∑ j ∈ s, a i * a j * (2 * ⟪v i, v j⟫_ℝ)
              = 2 * (∑ i ∈ s, ∑ j ∈ s, a i * a j * ⟪v i, v j⟫_ℝ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro j hj; ring
          rw [hscale, hinner, hnorm]
        rw [h1, h2, hcross]
        ring
    _ = 2 * ∑ i ∈ s, a i * ‖u i - z‖ ^ 2 - 2 * ‖∑ i ∈ s, a i • u i - z‖ ^ 2 := by
        rw [← hsumv]

private noncomputable def kirszbraunPotential
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [Fintype ι] (K : ℝ) (x : E) (xs : ι → E) (ys : ι → F) (a : ι → ℝ) : ℝ :=
  ∑ j, a j * ‖ys j‖ ^ 2 - ‖∑ j, a j • ys j‖ ^ 2 - K ^ 2 * ∑ j, a j * ‖x - xs j‖ ^ 2

private theorem kirszbraunPotential_perturb
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℝ) (x : E) (xs : ι → E) (ys : ι → F) (a : ι → ℝ) (i : ι) (t : ℝ) :
    kirszbraunPotential K x xs ys (fun j => (1 - t) * a j + t * ((Pi.single i 1 : ι → ℝ) j))
      = kirszbraunPotential K x xs ys a
        + t * (‖ys i - ∑ j, a j • ys j‖ ^ 2 - K ^ 2 * ‖x - xs i‖ ^ 2
          - kirszbraunPotential K x xs ys a)
        - t ^ 2 * ‖ys i - ∑ j, a j • ys j‖ ^ 2 := by
  set s : ι → ℝ := Pi.single i 1 with hs
  have hsval : ∀ j, s j = ((Pi.single i 1 : ι → ℝ) j) := fun j => rfl
  set ybar : F := ∑ j, a j • ys j with hybar
  set S1 : ℝ := ∑ j, a j * ‖ys j‖ ^ 2 with hS1
  set S2 : ℝ := ∑ j, a j * ‖x - xs j‖ ^ 2 with hS2
  set nY : ℝ := ‖ybar‖ ^ 2 with hnY
  have hssum1 : ∑ j, s j * ‖ys j‖ ^ 2 = ‖ys i‖ ^ 2 := by
    have h : ∑ j, s j * ‖ys j‖ ^ 2 = s i * ‖ys i‖ ^ 2 := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        have : s j = 0 := by
          simp [hs, hji]
        rw [this, zero_mul]
      · intro hi
        simp [Finset.mem_univ] at hi
    rw [h]
    simp [hs]
  have hssum2 : ∑ j, s j * ‖x - xs j‖ ^ 2 = ‖x - xs i‖ ^ 2 := by
    have h : ∑ j, s j * ‖x - xs j‖ ^ 2 = s i * ‖x - xs i‖ ^ 2 := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        have : s j = 0 := by
          simp [hs, hji]
        rw [this, zero_mul]
      · intro hi
        simp [Finset.mem_univ] at hi
    rw [h]
    simp [hs]
  have hssum3 : ∑ j, s j • ys j = ys i := by
    have h : ∑ j, s j • ys j = s i • ys i := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        have : s j = 0 := by
          simp [hs, hji]
        rw [this, zero_smul]
      · intro hi
        simp [Finset.mem_univ] at hi
    rw [h]
    simp [hs]
  have hP1 : ∑ j, ((1 - t) * a j + t * s j) * ‖ys j‖ ^ 2
      = (1 - t) * S1 + t * ‖ys i‖ ^ 2 := by
    have step : ∑ j, ((1 - t) * a j + t * s j) * ‖ys j‖ ^ 2
        = ∑ j, ((1 - t) * (a j * ‖ys j‖ ^ 2) + t * (s j * ‖ys j‖ ^ 2)) := by
      apply Finset.sum_congr rfl; intro j _; ring
    rw [step, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hssum1]
  have hP3 : ∑ j, ((1 - t) * a j + t * s j) * ‖x - xs j‖ ^ 2
      = (1 - t) * S2 + t * ‖x - xs i‖ ^ 2 := by
    have step : ∑ j, ((1 - t) * a j + t * s j) * ‖x - xs j‖ ^ 2
        = ∑ j, ((1 - t) * (a j * ‖x - xs j‖ ^ 2) + t * (s j * ‖x - xs j‖ ^ 2)) := by
      apply Finset.sum_congr rfl; intro j _; ring
    rw [step, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hssum2]
  have hP2 : (∑ j, ((1 - t) * a j + t * s j) • ys j)
      = (1 - t) • ybar + t • ys i := by
    have step : ∑ j, ((1 - t) * a j + t * s j) • ys j
        = ∑ j, ((1 - t) • (a j • ys j) + (t * s j) • ys j) := by
      apply Finset.sum_congr rfl; intro j _
      rw [add_smul, mul_smul]
    rw [step, Finset.sum_add_distrib, ← Finset.smul_sum]
    have hsecond : ∑ j, (t * s j) • ys j = t • ys i := by
      have : ∑ j, (t * s j) • ys j = t • (∑ j, s j • ys j) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl; intro j _
        rw [mul_smul]
      rw [this, hssum3]
    rw [hsecond]
  have hNorm : ‖(1 - t) • ybar + t • ys i‖ ^ 2
      = (1 - t) ^ 2 * nY + 2 * ((1 - t) * t) * ⟪ybar, ys i⟫_ℝ + t ^ 2 * ‖ys i‖ ^ 2 := by
    have h := norm_add_sq_real ((1 - t) • ybar) (t • ys i)
    rw [h]
    have e1 : ‖(1 - t) • ybar‖ ^ 2 = (1 - t) ^ 2 * nY := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have e2 : ‖t • ys i‖ ^ 2 = t ^ 2 * ‖ys i‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have e3 : ⟪(1 - t) • ybar, t • ys i⟫_ℝ = ((1 - t) * t) * ⟪ybar, ys i⟫_ℝ := by
      rw [real_inner_smul_left, real_inner_smul_right]; ring
    rw [e1, e2, e3]
    ring
  have hDiff : ‖ys i - ybar‖ ^ 2 = ‖ys i‖ ^ 2 - 2 * ⟪ybar, ys i⟫_ℝ + nY := by
    have h := norm_sub_sq_real (ys i) (ybar)
    have hc : ⟪ys i, ybar⟫_ℝ = ⟪ybar, ys i⟫_ℝ := real_inner_comm _ _
    simp only [hnY] at *
    linarith [h, hc]
  unfold kirszbraunPotential
  rw [hP1, hP2, hP3, hNorm]
  simp only [hS1, hS2, hnY, hybar] at *
  rw [hDiff]
  ring

-- N4: inline simplex is compact
private theorem kirszbraun_isCompact_simplex_fintype
    {ι : Type*} [Fintype ι] :
    IsCompact {a : ι → ℝ | (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1} := by
  apply IsCompact.of_isClosed_subset isCompact_Icc
  · -- closedness
    have h1 : IsClosed {a : ι → ℝ | ∀ i, 0 ≤ a i} := by
      have : {a : ι → ℝ | ∀ i, 0 ≤ a i} = ⋂ i, {a : ι → ℝ | 0 ≤ a i} := by
        ext a; simp [Set.mem_iInter]
      rw [this]
      apply isClosed_iInter
      intro i
      exact isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed {a : ι → ℝ | ∑ i, a i = 1} := by
      apply isClosed_eq _ continuous_const
      apply continuous_finsetSum _ (fun i _ => continuous_apply i)
    have hinter : IsClosed ({a : ι → ℝ | (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1}) := by
      have : {a : ι → ℝ | (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1}
          = {a : ι → ℝ | ∀ i, 0 ≤ a i} ∩ {a : ι → ℝ | ∑ i, a i = 1} := by
        ext a; simp [Set.mem_inter_iff]
      rw [this]
      exact h1.inter h2
    exact hinter
  · -- subset of Icc 0 1
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha
    obtain ⟨hnn, hsum⟩ := ha
    constructor
    · intro i
      exact hnn i
    · intro i
      simp only
      -- a i ≤ 1 via single_le_sum
      have hle : a i ≤ ∑ j, a j := by
        apply Finset.single_le_sum (fun j _ => hnn j)
        exact Finset.mem_univ i
      rw [hsum] at hle
      simpa using hle

private theorem kirszbraun_exists_mem_norm_sub_sq_le_of_convex
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {C : Set F} (hne : C.Nonempty) (hcomp : IsComplete C) (hconv : Convex ℝ C) :
    ∃ p ∈ C, ∀ z ∈ C, ‖z - p‖ ^ 2 ≤ ‖z‖ ^ 2 - ‖p‖ ^ 2 := by
  obtain ⟨p, hpC, hinf⟩ := exists_norm_eq_iInf_of_complete_convex hne hcomp hconv (0 : F)
  refine ⟨p, hpC, fun z hz => ?_⟩
  have hchar := (norm_eq_iInf_iff_real_inner_le_zero hconv hpC).mp hinf z hz
  simp only [zero_sub] at hchar
  have hexpand : ‖z‖ ^ 2 = ‖z - p‖ ^ 2 + 2 * ⟪z - p, p⟫_ℝ + ‖p‖ ^ 2 := by
    have h := norm_add_sq_real (z - p) p
    have hzp : (z - p) + p = z := sub_add_cancel z p
    rw [hzp] at h
    linarith [h]
  have hcomm : ⟪z - p, p⟫_ℝ = ⟪p, z - p⟫_ℝ := real_inner_comm _ _
  have hneg : ⟪-p, z - p⟫_ℝ = -⟪p, z - p⟫_ℝ := inner_neg_left _ _
  have hpos : 0 ≤ ⟪z - p, p⟫_ℝ := by linarith [hchar, hcomm, hneg]
  linarith [hexpand, hpos]

private theorem kirszbraun_cauchySeq_of_dist_sq_le_sub
    {β : Type*} [SemilatticeSup β] [Nonempty β]
    {X : Type*} [PseudoMetricSpace X]
    (p : β → X) (d : β → ℝ)
    (hbdd : BddAbove (Set.range d))
    (hdec : ∀ a b : β, a ≤ b → dist (p a) (p b) ^ 2 ≤ d b - d a) :
    CauchySeq p := by
  have hmono : Monotone d := fun a b hab => by
    have h := hdec a b hab
    have hnn : 0 ≤ dist (p a) (p b) ^ 2 := sq_nonneg _
    linarith
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have hlt : iSup d - ε ^ 2 < iSup d := by
    have : 0 < ε ^ 2 := by positivity
    linarith
  obtain ⟨N0, hN⟩ := exists_lt_of_lt_ciSup hlt
  refine ⟨N0, fun n hn => ?_⟩
  have hle : dist (p N0) (p n) ^ 2 ≤ d n - d N0 := hdec N0 n hn
  have hdn_le : d n ≤ iSup d := le_ciSup hbdd n
  have hcomm : dist (p n) (p N0) = dist (p N0) (p n) := dist_comm _ _
  have hsq : dist (p n) (p N0) ^ 2 < ε ^ 2 := by
    rw [hcomm]
    linarith [hle, hdn_le, hN]
  have hnn1 : 0 ≤ dist (p n) (p N0) := dist_nonneg
  have hnn2 : 0 ≤ ε := le_of_lt hε
  have hlt2 := (sq_lt_sq₀ hnn1 hnn2).mp hsq
  linarith [hlt2]
-- N2: potential nonpositive
private theorem kirszbraunPotential_nonpos
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [Fintype ι]
    (K : ℝ) (x : E) (xs : ι → E) (ys : ι → F)
    (hlip : ∀ i j, ‖ys i - ys j‖ ≤ K * ‖xs i - xs j‖)
    (a : ι → ℝ) (hnn : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1) :
    kirszbraunPotential K x xs ys a ≤ 0 := by
  have hsumU : ∑ i ∈ Finset.univ, a i = 1 := hsum
  have hN1y := kirszbraun_sum_mul_mul_norm_sub_sq_eq (G := F) Finset.univ a ys 0 hsumU
  have hN1x := kirszbraun_sum_mul_mul_norm_sub_sq_eq (G := E) Finset.univ a xs x hsumU
  simp only [sub_zero] at hN1y
  set Dys : ℝ := ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, a i * a j * ‖ys i - ys j‖ ^ 2 with hDys
  set Dxs : ℝ := ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, a i * a j * ‖xs i - xs j‖ ^ 2 with hDxs
  set S2 : ℝ := ∑ j, a j * ‖x - xs j‖ ^ 2 with hS2
  have hterm : ∀ i j, a i * a j * ‖ys i - ys j‖ ^ 2 ≤ a i * a j * (K ^ 2 * ‖xs i - xs j‖ ^ 2) := by
    intro i j
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hnn i) (hnn j))
    have h := hlip i j
    have hnn0 : (0 : ℝ) ≤ ‖ys i - ys j‖ := norm_nonneg _
    have hKnn : (0 : ℝ) ≤ K * ‖xs i - xs j‖ := le_trans hnn0 h
    have hsq := pow_le_pow_left₀ hnn0 h 2
    rwa [mul_pow] at hsq
  have hD : Dys ≤ ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, a i * a j *
      (K ^ 2 * ‖xs i - xs j‖ ^ 2) := by
    simp only [hDys]
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    exact hterm i j
  have hK : (∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, a i * a j * (K ^ 2 * ‖xs i - xs j‖ ^ 2)) = K ^ 2
      * Dxs := by
    simp only [hDxs]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  have hX : Dxs ≤ 2 * S2 := by
    have hnn2 : (0 : ℝ) ≤ ‖(∑ i ∈ Finset.univ, a i • xs i) - x‖ ^ 2 := sq_nonneg _
    have hrev : (∑ i ∈ Finset.univ, a i * ‖xs i - x‖ ^ 2) = S2 := by
      simp only [hS2]
      apply Finset.sum_congr rfl; intro j _
      congr 1
      rw [norm_sub_rev]
    simp only [hDxs] at *
    linarith [hN1x, hnn2, hrev]
  have hDx : Dys ≤ K ^ 2 * Dxs := by rw [← hK]; exact hD
  have hK2 : (0 : ℝ) ≤ K ^ 2 := sq_nonneg _
  have hprod : K ^ 2 * Dxs ≤ K ^ 2 * (2 * S2) := mul_le_mul_of_nonneg_left hX hK2
  simp only [hDys] at hN1y
  unfold kirszbraunPotential
  linarith [hN1y, hDx, hprod]
-- N5: finite Kirszbraun lemma
private theorem kirszbraun_exists_forall_norm_sub_le_of_fintype
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [Finite ι]
    (K : ℝ) (hK : 0 ≤ K) (x : E) (xs : ι → E) (ys : ι → F)
    (hlip : ∀ i j, ‖ys i - ys j‖ ≤ K * ‖xs i - xs j‖) :
    ∃ y : F, ∀ i, ‖y - ys i‖ ≤ K * ‖x - xs i‖ := by
  classical
  have := Fintype.ofFinite ι
  by_cases hempty : IsEmpty ι
  · exact ⟨0, fun i => (hempty.false i).elim⟩
  · rw [not_isEmpty_iff] at hempty
    obtain ⟨i0⟩ := hempty
    -- simplex set
    set Δ : Set (ι → ℝ) := {a : ι → ℝ | (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1} with hΔ
    have hcompact : IsCompact Δ := kirszbraun_isCompact_simplex_fintype
    have hne : Δ.Nonempty := by
      refine ⟨Pi.single i0 1, ?_, ?_⟩
      · intro j
        by_cases hji : j = i0
        · subst hji; rw [Pi.single_eq_same]; exact zero_le_one
        · rw [Pi.single_eq_of_ne hji]
      · rw [Fintype.sum_pi_single' i0 1]
    -- continuity of potential
    have hcont1 : Continuous (fun a : ι → ℝ => ∑ j, a j * ‖ys j‖ ^ 2) := by
      apply continuous_finsetSum Finset.univ (fun j _ => ?_)
      exact (continuous_apply j).mul continuous_const
    have hcont3 : Continuous (fun a : ι → ℝ => ∑ j, a j * ‖x - xs j‖ ^ 2) := by
      apply continuous_finsetSum Finset.univ (fun j _ => ?_)
      exact (continuous_apply j).mul continuous_const
    have hcontB : Continuous (fun a : ι → ℝ => ∑ j, a j • ys j) := by
      apply continuous_finsetSum Finset.univ (fun j _ => ?_)
      exact (continuous_apply j).smul continuous_const
    have hcont : Continuous (fun a : ι → ℝ => kirszbraunPotential K x xs ys a) := by
      unfold kirszbraunPotential
      apply Continuous.sub
      · apply Continuous.sub
        · exact hcont1
        · exact (hcontB.norm.pow 2)
      · exact (hcont3.const_mul (K ^ 2))
    obtain ⟨astar, hstar_mem, hstar_max⟩ :=
      hcompact.exists_isMaxOn hne hcont.continuousOn
    have hstar_nn : ∀ j, 0 ≤ astar j := (hstar_mem.1)
    have hstar_sum : ∑ i, astar i = 1 := (hstar_mem.2)
    set y : F := ∑ j, astar j • ys j with hy
    have hPhi_le : kirszbraunPotential K x xs ys astar ≤ 0 :=
      kirszbraunPotential_nonpos K x xs ys hlip astar hstar_nn hstar_sum
    refine ⟨y, fun i => ?_⟩
    -- perturbation analysis at i
    have hmem : ∀ t : ℝ, 0 < t → t ≤ 1 →
        (fun j => (1 - t) * astar j + t * ((Pi.single i 1 : ι → ℝ) j)) ∈ Δ := by
      intro t ht0 ht1
      constructor
      · intro j
        apply add_nonneg
        · apply mul_nonneg (by linarith) (hstar_nn j)
        · apply mul_nonneg (le_of_lt ht0)
          by_cases hji : j = i
          · subst hji; rw [Pi.single_eq_same]; exact zero_le_one
          · rw [Pi.single_eq_of_ne hji]
      · -- sum = (1-t)*1 + t*1
        have e1 : ∑ j, (1 - t) * astar j = (1 - t) := by
          rw [← Finset.mul_sum, hstar_sum, mul_one]
        have e2 : ∑ j, t * ((Pi.single i 1 : ι → ℝ) j) = t := by
          rw [← Finset.mul_sum, Fintype.sum_pi_single' i 1, mul_one]
        have : ∑ j, ((1 - t) * astar j + t * ((Pi.single i 1 : ι → ℝ) j))
            = ∑ j, (1 - t) * astar j + ∑ j, t * ((Pi.single i 1 : ι → ℝ) j) := by
          rw [Finset.sum_add_distrib]
        rw [this, e1, e2]
        ring
    -- D ≤ t * c for t ∈ (0,1]
    set D : ℝ := ‖ys i - y‖ ^ 2 - K ^ 2 * ‖x - xs i‖ ^ 2 - kirszbraunPotential K x xs ys astar with
        hD
    set c : ℝ := ‖ys i - y‖ ^ 2 with hc
    have hstep : ∀ t : ℝ, 0 < t → t ≤ 1 → D ≤ t * c := by
      intro t ht0 ht1
      have hle := (isMaxOn_iff.mp hstar_max) _ (hmem t ht0 ht1)
      have hpert := kirszbraunPotential_perturb (K := K) (x := x) (xs := xs) (ys := ys) (a := astar)
          (i := i) (t := t)
      simp only [hy, hc, hD] at *
      -- hle : Φ(a_t) ≤ Φ(a*); hpert : Φ(a_t) = Φ(a*) + t*(...) - t^2*c
      rw [hpert] at hle
      have htd : t * (‖ys i - y‖ ^ 2 - K ^ 2 * ‖x - xs i‖ ^ 2 - kirszbraunPotential K x xs ys astar)
          ≤ t ^ 2 * ‖ys i - y‖ ^ 2 := by
        linarith [hle]
      have htd2 : t * (‖ys i - y‖ ^ 2 - K ^ 2 * ‖x - xs i‖ ^ 2 - kirszbraunPotential K x xs ys
          astar) ≤ t * (t * ‖ys i - y‖ ^ 2) := by
        have : t ^ 2 * ‖ys i - y‖ ^ 2 = t * (t * ‖ys i - y‖ ^ 2) := by ring
        linarith [htd, this]
      have := le_of_mul_le_mul_left htd2 ht0
      simpa [hD, hc] using this
    -- D ≤ 0
    have hD0 : D ≤ 0 := by
      apply le_of_forall_pos_le_add
      intro ε hε
      have hcn : (0:ℝ) ≤ c := sq_nonneg _
      set u : ℝ := min 1 (ε / (c + 1)) with hu
      have hu0 : 0 < u := lt_min (by norm_num) (by positivity)
      have hu1 : u ≤ 1 := min_le_left _ _
      have hDu := hstep u hu0 hu1
      have hur : u ≤ ε / (c + 1) := min_le_right _ _
      have huc : u * c ≤ (ε / (c + 1)) * c := mul_le_mul_of_nonneg_right hur hcn
      have hpos : (0:ℝ) < c + 1 := by linarith [hcn]
      have hfin : (ε / (c + 1)) * c ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
        have : ε * c ≤ ε * (c + 1) := by
          have : ε * (c + 1) = ε * c + ε := by ring
          linarith [hε, this]
        linarith [this]
      linarith [hDu, huc, hfin]
    -- conclude norm bound
    have hsq : ‖ys i - y‖ ^ 2 ≤ (K * ‖x - xs i‖) ^ 2 := by
      have : (K * ‖x - xs i‖) ^ 2 = K ^ 2 * ‖x - xs i‖ ^ 2 := by ring
      simp only [hD, hc] at hD0
      linarith [hD0, hPhi_le, this]
    have h1 : (0:ℝ) ≤ ‖y - ys i‖ := norm_nonneg _
    have h2 : (0:ℝ) ≤ K * ‖x - xs i‖ := mul_nonneg hK (norm_nonneg _)
    have hsq2 : ‖y - ys i‖ ^ 2 ≤ (K * ‖x - xs i‖) ^ 2 := by
      have e : ‖y - ys i‖ = ‖ys i - y‖ := norm_sub_rev _ _
      rw [e]
      exact hsq
    exact (sq_le_sq₀ h1 h2).mp hsq2
-- N8: Hilbert finite-intersection lemma
private theorem kirszbraun_exists_mem_iInter_of_convex_of_finite_inter
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {ι : Type*} (C : ι → Set F) (i₀ : ι)
    (hclosed : ∀ i, IsClosed (C i)) (hconv : ∀ i, Convex ℝ (C i))
    (hbdd : Bornology.IsBounded (C i₀))
    (hfin : ∀ A : Finset ι, ∃ y, ∀ i ∈ A, y ∈ C i) :
    ∃ y, ∀ i, y ∈ C i := by
  classical
  set D : Finset ι → Set F := fun A => C i₀ ∩ ⋂ i ∈ (↑A : Set ι), C i with hD
  have hDclosed : ∀ A, IsClosed (D A) := by
    intro A
    apply IsClosed.inter (hclosed i₀)
    apply isClosed_biInter
    intro i _
    exact hclosed i
  have hDconv : ∀ A, Convex ℝ (D A) := by
    intro A
    apply Convex.inter (hconv i₀)
    apply convex_iInter₂
    intro i _
    exact hconv i
  have hDne : ∀ A, (D A).Nonempty := by
    intro A
    obtain ⟨y, hy⟩ := hfin (insert i₀ A)
    refine ⟨y, hy i₀ (Finset.mem_insert_self i₀ A), Set.mem_biInter (fun i hi => ?_)⟩
    exact hy i (Finset.mem_insert_of_mem (Finset.mem_coe.mp hi))
  have hex : ∀ A : Finset ι, ∃ pA ∈ D A, ∀ z ∈ D A, ‖z - pA‖ ^ 2 ≤ ‖z‖ ^ 2 - ‖pA‖ ^ 2 := by
    intro A
    exact kirszbraun_exists_mem_norm_sub_sq_le_of_convex (hDne A) ((hDclosed A).isComplete)
        (hDconv A)
  choose p hp using hex
  -- boundedness of norms
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : F)).mp hbdd
  have hbdd2 : BddAbove (Set.range (fun A : Finset ι => ‖p A‖ ^ 2)) := by
    refine ⟨r ^ 2, ?_⟩
    rintro _ ⟨A, rfl⟩
    have hmem0 : p A ∈ C i₀ := (hp A).1.1
    have h1 : ‖p A‖ ≤ r := by
      have hball := hr hmem0
      rw [mem_closedBall_iff_norm, sub_zero] at hball
      exact hball
    have h2 : ‖p A‖ ≤ |r| := le_trans h1 (le_abs_self r)
    have h3 := pow_le_pow_left₀ (norm_nonneg (p A)) h2 2
    rwa [sq_abs] at h3
  -- Cauchy
  have hcauchy : CauchySeq p := by
    apply kirszbraun_cauchySeq_of_dist_sq_le_sub _ _ hbdd2
    intro A B hAB
    have hsub : D B ⊆ D A := by
      intro z hz
      obtain ⟨hz0, hzB⟩ := hz
      refine ⟨hz0, Set.mem_biInter (fun i hi => ?_)⟩
      simp only [Set.mem_iInter] at hzB
      exact hzB i (Finset.mem_coe.mpr (hAB (Finset.mem_coe.mp hi)))
    have hmemBA : p B ∈ D A := hsub (hp B).1
    have h := (hp A).2 (p B) hmemBA
    rw [dist_eq_norm, norm_sub_rev]
    exact h
  obtain ⟨y, hylim⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨y, fun i => ?_⟩
  have hev : ∀ᶠ A in Filter.atTop, p A ∈ C i := by
    have h := Filter.eventually_ge_atTop ({i} : Finset ι)
    apply h.mono
    intro A hA
    have hiA : i ∈ A := hA (Finset.mem_singleton_self i)
    have h2 := (hp A).1.2
    simp only [Set.mem_iInter] at h2
    exact h2 i (Finset.mem_coe.mpr hiA)
  exact (hclosed i).mem_of_tendsto hylim hev
-- N9: finite lemma, Finset form
private theorem kirszbraun_exists_forall_norm_sub_le_of_finset
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} (A : Finset ι)
    (K : ℝ) (hK : 0 ≤ K) (x : E) (xs : ι → E) (ys : ι → F)
    (hlip : ∀ i ∈ A, ∀ j ∈ A, ‖ys i - ys j‖ ≤ K * ‖xs i - xs j‖) :
    ∃ y : F, ∀ i ∈ A, ‖y - ys i‖ ≤ K * ‖x - xs i‖ := by
  have h5 := kirszbraun_exists_forall_norm_sub_le_of_fintype (ι := ↥A) K hK x
    (fun a : ↥A => xs a) (fun a : ↥A => ys a) (fun a b => hlip a a.2 b b.2)
  obtain ⟨y, hy⟩ := h5
  exact ⟨y, fun i hi => hy ⟨i, hi⟩⟩

-- N10: one-point extension
private theorem kirszbraun_exists_norm_sub_le_of_compatible_graph
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (K : ℝ) (hK : 0 ≤ K) (G : Set (E × F))
    (hG : ∀ q ∈ G, ∀ q' ∈ G, ‖q.2 - q'.2‖ ≤ K * ‖q.1 - q'.1‖)
    (x : E) :
    ∃ y : F, ∀ q ∈ G, ‖y - q.2‖ ≤ K * ‖x - q.1‖ := by
  by_cases hempty : G.Nonempty
  · obtain ⟨q₀, hq₀⟩ := hempty
    have hfin : ∀ A : Finset ↥G, ∃ y, ∀ q ∈ A,
        y ∈ Metric.closedBall (q : E × F).2 (K * ‖x - (q : E × F).1‖) := by
      intro A
      have h9 := kirszbraun_exists_forall_norm_sub_le_of_finset (ι := ↥G) A K hK x
        (fun q => (q : E × F).1) (fun q => (q : E × F).2)
        (fun a ha b hb => hG a a.2 b b.2)
      obtain ⟨y, hy⟩ := h9
      refine ⟨y, fun q hq => ?_⟩
      have h := hy q hq
      rw [mem_closedBall_iff_norm]
      exact h
    obtain ⟨y, hy⟩ := kirszbraun_exists_mem_iInter_of_convex_of_finite_inter
      (fun q : ↥G => Metric.closedBall (q : E × F).2 (K * ‖x - (q : E × F).1‖))
      ⟨q₀, hq₀⟩ (fun q => Metric.isClosed_closedBall)
      (fun q => convex_closedBall _ _)
      Metric.isBounded_closedBall hfin
    refine ⟨y, fun q hq => ?_⟩
    have h := hy ⟨q, hq⟩
    rw [mem_closedBall_iff_norm] at h
    exact h
  · rw [Set.not_nonempty_iff_eq_empty] at hempty
    refine ⟨0, fun q hq => ?_⟩
    rw [hempty] at hq
    exact (Set.notMem_empty q hq).elim

-- N11: Zorn maximal compatible graph
private theorem kirszbraun_exists_maximal_compatible_graph
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (s : Set E) (f : E → F) (K : ℝ)
    (hlip : ∀ a ∈ s, ∀ b ∈ s, ‖f a - f b‖ ≤ K * ‖a - b‖) :
    ∃ G, Maximal (fun H : Set (E × F) =>
      (∀ a ∈ s, (a, f a) ∈ H) ∧ ∀ q ∈ H, ∀ q' ∈ H, ‖q.2 - q'.2‖ ≤ K * ‖q.1 - q'.1‖) G := by
  have h := zorn_subset {G : Set (E × F) |
    (∀ a ∈ s, (a, f a) ∈ G) ∧ ∀ q ∈ G, ∀ q' ∈ G, ‖q.2 - q'.2‖ ≤ K * ‖q.1 - q'.1‖} ?_
  · exact h
  · intro c hcsub hchain
    refine ⟨(fun a => (a, f a)) '' s ∪ ⋃₀ c, ?_, ?_⟩
    · constructor
      · intro a ha
        exact Set.mem_union_left _ (Set.mem_image_of_mem _ ha)
      · intro q hq q' hq'
        rcases hq with hqimg | hqU
        · rcases hq' with hq'img | hq'U
          · obtain ⟨a, ha, rfl⟩ := hqimg
            obtain ⟨b, hb, rfl⟩ := hq'img
            exact hlip a ha b hb
          · obtain ⟨a, ha, rfl⟩ := hqimg
            obtain ⟨G, hGc, hGq⟩ := Set.mem_sUnion.mp hq'U
            have hGS := hcsub hGc
            rw [Set.mem_ofPred_eq] at hGS
            exact hGS.2 (a, f a) (hGS.1 a ha) q' hGq
        · rcases hq' with hq'img | hq'U
          · obtain ⟨b, hb, rfl⟩ := hq'img
            obtain ⟨G, hGc, hGq⟩ := Set.mem_sUnion.mp hqU
            have hGS := hcsub hGc
            rw [Set.mem_ofPred_eq] at hGS
            exact hGS.2 q hGq (b, f b) (hGS.1 b hb)
          · obtain ⟨G₁, hG₁c, hG₁q⟩ := Set.mem_sUnion.mp hqU
            obtain ⟨G₂, hG₂c, hG₂q⟩ := Set.mem_sUnion.mp hq'U
            have hGS₁ := hcsub hG₁c
            have hGS₂ := hcsub hG₂c
            rw [Set.mem_ofPred_eq] at hGS₁ hGS₂
            rcases hchain.total hG₁c hG₂c with h12 | h21
            · exact hGS₂.2 q (h12 hG₁q) q' hG₂q
            · exact hGS₁.2 q hG₁q q' (h21 hG₂q)
    · intro G' hG'
      refine le_trans ?_ Set.subset_union_right
      intro z hz
      exact Set.mem_sUnion.mpr ⟨G', hG', hz⟩

-- N12: maximal graph is total
private theorem kirszbraun_compatible_graph_total_of_maximal
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (s : Set E) (f : E → F) (K : ℝ) (hK : 0 ≤ K)
    (G : Set (E × F))
    (hGmem : (∀ a ∈ s, (a, f a) ∈ G) ∧ ∀ q ∈ G, ∀ q' ∈ G, ‖q.2 - q'.2‖ ≤ K * ‖q.1 - q'.1‖)
    (hmax : Maximal (fun H : Set (E × F) =>
      (∀ a ∈ s, (a, f a) ∈ H) ∧ ∀ q ∈ H, ∀ q' ∈ H, ‖q.2 - q'.2‖ ≤ K * ‖q.1 - q'.1‖) G) :
    ∀ x : E, ∃ y, (x, y) ∈ G := by
  intro x
  obtain ⟨y, hy⟩ := kirszbraun_exists_norm_sub_le_of_compatible_graph K hK G hGmem.2 x
  have hins : (∀ a ∈ s, (a, f a) ∈ insert (x, y) G) ∧
      ∀ q ∈ insert (x, y) G, ∀ q' ∈ insert (x, y) G, ‖q.2 - q'.2‖ ≤ K * ‖q.1 - q'.1‖ := by
    constructor
    · intro a ha
      exact Set.mem_insert_iff.mpr (Or.inr (hGmem.1 a ha))
    · intro q hq q' hq'
      rcases Set.mem_insert_iff.mp hq with rfl | hqG
      · rcases Set.mem_insert_iff.mp hq' with rfl | hq'G
        · rw [sub_self, sub_self, norm_zero, norm_zero]
          exact mul_nonneg hK (le_refl 0)
        · exact hy q' hq'G
      · rcases Set.mem_insert_iff.mp hq' with rfl | hq'G
        · have h := hy q hqG
          rw [norm_sub_rev y q.2, norm_sub_rev x q.1] at h
          exact h
        · exact hGmem.2 q hqG q' hq'G
  have heq := hmax.eq_of_subset hins (Set.subset_insert (x, y) G)
  rw [heq]
  exact ⟨y, Set.mem_insert (x, y) G⟩



section
namespace MathlibExt.Analysis.InnerProductSpace.KirszbraunWanted

/--
**Kirszbraun extension theorem.** Let $E$ be a real inner product space (not necessarily
complete), let $F$ be a complete real inner product space, let $s \subseteq E$ and let $K \ge 0$.
Every map $f : E \to F$ that is $K$-Lipschitz on $s$ agrees on $s$ with some map
$g : E \to F$ that is $K$-Lipschitz on all of $E$.

Proves `Wanted` entry `kirszbraun`.

Source: M. Kirszbraun, Fund. Math.
22 (1934) 77-108 thesis; Valentine 1945 extension to Hilbert; Federer, Geometric Measure Theory,
2.10.43; the Lean theorem takes a real inner-product-space domain `E` and a complete real
inner-product-space target `F`, with the same Lipschitz constant `LipschitzWith K`.
-/
theorem kirszbraun_general
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {s : Set E} {K : NNReal} {f : E → F}
    (hf : LipschitzOnWith K f s) :
    ∃ g : E → F, LipschitzWith K g ∧ Set.EqOn f g s := by
  have hlip : ∀ a ∈ s, ∀ b ∈ s, ‖f a - f b‖ ≤ (K : ℝ) * ‖a - b‖ := by
    intro a ha b hb
    have h := hf.dist_le_mul a ha b hb
    rwa [dist_eq_norm, dist_eq_norm] at h
  obtain ⟨G, hmax⟩ := kirszbraun_exists_maximal_compatible_graph s f (K : ℝ) hlip
  have hGmem := hmax.1
  have htotal := kirszbraun_compatible_graph_total_of_maximal s f (K : ℝ)
    (NNReal.coe_nonneg K) G hGmem hmax
  choose g hg using htotal
  refine ⟨g, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x x'
    have h := hGmem.2 (x, g x) (hg x) (x', g x') (hg x')
    rw [dist_eq_norm, dist_eq_norm]
    exact h
  · intro a ha
    have h1 : (a, f a) ∈ G := hGmem.1 a ha
    have h2 : (a, g a) ∈ G := hg a
    have h := hGmem.2 (a, f a) h1 (a, g a) h2
    rw [sub_self, norm_zero, mul_zero] at h
    have hzero : f a - g a = 0 := norm_le_zero_iff.mp h
    exact sub_eq_zero.mp hzero

/--
**Kirszbraun extension theorem for Hilbert spaces.** Let $E$ and $F$ be real Hilbert spaces,
let $s \subseteq E$ and let $K \ge 0$. Every map $f : E \to F$ that is $K$-Lipschitz on $s$
agrees on $s$ with some map $g : E \to F$ that is $K$-Lipschitz on all of $E$.

Completeness of $E$ is not used: this is a special case of the Kirszbraun extension theorem for
an arbitrary real inner product space domain.
-/
@[nolint unusedArguments]
theorem kirszbraun
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {s : Set E} {K : NNReal} {f : E → F}
    (hf : LipschitzOnWith K f s) :
    ∃ g : E → F, LipschitzWith K g ∧ Set.EqOn f g s :=
  kirszbraun_general hf

end MathlibExt.Analysis.InnerProductSpace.KirszbraunWanted
end

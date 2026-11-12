/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

/-! # Volumetric covering bound

The closed ball of radius `R` in `EuclideanSpace ℝ (Fin m)` has an
`ε`-net of at most `(1 + 2R/ε)^m` points, by the volumetric
argument (a maximal `ε`-separated set, disjoint `ε/2`-balls, and a
volume comparison). This is the covering input of roadmap package
ML-31 of the Atlas TCS canon roadmap; Dudley's entropy integral is
a follow-up.

Source: Vershynin, High-Dimensional Probability (2018),
Proposition 4.2.12.
-/

open Metric

/-- Volumetric covering bound: the closed ball of radius `R` in
`EuclideanSpace ℝ (Fin m)` has an `ε`-net of at most
`(1 + 2R/ε)^m` points (the bound is stated over the reals). -/
theorem euclidean_ball_net {m : ℕ} {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ C : Finset (EuclideanSpace ℝ (Fin m)),
      (∀ x ∈ C, ‖x‖ ≤ R + ε) ∧
      (∀ x, ‖x‖ ≤ R → ∃ c ∈ C, dist x c ≤ ε) ∧
      (C.card : ℝ) ≤ (1 + 2 * R / ε) ^ m := by
  classical
  have hεne : ε ≠ 0 := ne_of_gt hε
  have vol : ∀ C : Finset (EuclideanSpace ℝ (Fin m)),
      (∀ c ∈ C, ‖c‖ ≤ R) →
      (C : Set (EuclideanSpace ℝ (Fin m))).Pairwise (fun c d => ε ≤ dist c d) →
      (C.card : ℝ) ≤ (1 + 2 * R / ε) ^ m := by
    intro C hCR hsep
    set δ : ℝ := ε / 2 with hδ
    set ρ : ℝ := R + ε / 2 with hρ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    have hρpos : 0 < ρ := by rw [hρ]; linarith
    have hdisj : (C : Set (EuclideanSpace ℝ (Fin m))).PairwiseDisjoint (fun c => ball c δ) := by
      intro c hc d hd hcd
      have h := hsep hc hd hcd
      have h2 : δ + δ = ε := by rw [hδ]; ring
      show Disjoint (ball c δ) (ball d δ)
      apply Metric.ball_disjoint_ball
      linarith
    have hsub : (⋃ c ∈ C, ball c δ) ⊆ ball (0 : EuclideanSpace ℝ (Fin m)) ρ := by
      intro y hy
      simp only [Set.mem_iUnion, exists_prop] at hy
      obtain ⟨c, hc, hyc⟩ := hy
      rw [Metric.mem_ball] at hyc ⊢
      have hcR := hCR c hc
      have h1 : dist c (0 : EuclideanSpace ℝ (Fin m)) = ‖c‖ := by
        rw [dist_eq_norm, sub_zero]
      have h3 : dist c 0 + dist y c < R + δ :=
        add_lt_add_of_le_of_lt (by rw [h1]; exact hcR) hyc
      have hρeq : R + δ = ρ := by rw [hρ, hδ]
      have htri := dist_triangle y c (0 : EuclideanSpace ℝ (Fin m))
      linarith
    have hsmall : ∀ c ∈ C, MeasureTheory.volume (ball c δ)
        = ENNReal.ofReal (δ ^ m) * MeasureTheory.volume (ball (0 : EuclideanSpace ℝ (Fin m)) 1) := by
      intro c _
      have hh := MeasureTheory.Measure.addHaar_ball_of_pos MeasureTheory.volume c hδpos
      rwa [finrank_euclideanSpace_fin] at hh
    have hbig : MeasureTheory.volume (ball (0 : EuclideanSpace ℝ (Fin m)) ρ)
        = ENNReal.ofReal (ρ ^ m) * MeasureTheory.volume (ball (0 : EuclideanSpace ℝ (Fin m)) 1) := by
      have hh := MeasureTheory.Measure.addHaar_ball_of_pos MeasureTheory.volume
        (0 : EuclideanSpace ℝ (Fin m)) hρpos
      rwa [finrank_euclideanSpace_fin] at hh
    have hvol : (C.card : ENNReal) * ENNReal.ofReal (δ ^ m) *
          MeasureTheory.volume (ball (0 : EuclideanSpace ℝ (Fin m)) 1)
        ≤ ENNReal.ofReal (ρ ^ m) * MeasureTheory.volume (ball (0 : EuclideanSpace ℝ (Fin m)) 1) := by
      have hmono : MeasureTheory.volume (⋃ c ∈ C, ball c δ)
          ≤ MeasureTheory.volume (ball (0 : EuclideanSpace ℝ (Fin m)) ρ) :=
        MeasureTheory.measure_mono hsub
      rw [MeasureTheory.measure_biUnion_finset hdisj (fun c _ => measurableSet_ball),
        Finset.sum_congr rfl hsmall, Finset.sum_const, nsmul_eq_mul, hbig] at hmono
      simpa [mul_assoc] using hmono
    have hpos : (0 : ENNReal) < MeasureTheory.volume (ball (0 : EuclideanSpace ℝ (Fin m)) 1) :=
      Metric.measure_ball_pos _ _ zero_lt_one
    have hfin : MeasureTheory.volume (ball (0 : EuclideanSpace ℝ (Fin m)) 1) < ⊤ :=
      MeasureTheory.measure_ball_lt_top
    have hcancel : (C.card : ENNReal) * ENNReal.ofReal (δ ^ m) ≤ ENNReal.ofReal (ρ ^ m) :=
      (ENNReal.mul_le_mul_iff_left hpos.ne' hfin.ne).mp hvol
    have h2 : (C.card : ℝ) * δ ^ m ≤ ρ ^ m := by
      have h3 := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρpos.le m) hcancel
      rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ENNReal.toReal_ofReal (pow_nonneg hδpos.le m)] at h3
    have hdiv : (C.card : ℝ) ≤ ρ ^ m / δ ^ m := by
      rw [le_div_iff₀ (pow_pos hδpos m)]
      exact h2
    have hratio : ρ ^ m / δ ^ m = (1 + 2 * R / ε) ^ m := by
      rw [← div_pow]
      congr 1
      rw [hρ, hδ]
      have hε2 : ε / 2 ≠ 0 := div_ne_zero hεne two_ne_zero
      field_simp
      ring
    rw [hratio] at hdiv
    exact hdiv
  set B : ℝ := (1 + 2 * R / ε) ^ m with hB
  set N : ℕ := ⌊B⌋₊ with hN
  have hcard : ∀ C : Finset (EuclideanSpace ℝ (Fin m)),
      (∀ c ∈ C, ‖c‖ ≤ R) → (C : Set (EuclideanSpace ℝ (Fin m))).Pairwise (fun c d => ε ≤ dist c d) → C.card ≤ N := by
    intro C hCR hsep
    rw [hN]
    apply Nat.le_floor
    exact vol C hCR hsep
  set S : Finset ℕ := (Finset.Icc 0 N).filter (fun k =>
    ∃ C : Finset (EuclideanSpace ℝ (Fin m)), (∀ c ∈ C, ‖c‖ ≤ R) ∧
      (C : Set (EuclideanSpace ℝ (Fin m))).Pairwise (fun c d => ε ≤ dist c d) ∧ C.card = k) with hS
  have h0mem : 0 ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨le_rfl, Nat.zero_le N⟩, ∅, ?_, ?_, Finset.card_empty⟩
    · intro c hc
      exact (Finset.notMem_empty c hc).elim
    · intro a ha b hb hab
      simp only [Finset.coe_empty, Set.mem_empty_iff_false] at ha
  have hne : S.Nonempty := ⟨0, h0mem⟩
  obtain ⟨k, hk_mem, hk_max⟩ : ∃ k ∈ S, ∀ j ∈ S, j ≤ k :=
    ⟨S.max' hne, Finset.max'_mem S hne, fun j hj => Finset.le_max' S j hj⟩
  rw [hS, Finset.mem_filter, Finset.mem_Icc] at hk_mem
  obtain ⟨⟨-, hkN⟩, C, hCR, hsep, hCcard⟩ := hk_mem
  have hcov : ∀ x, ‖x‖ ≤ R → ∃ c ∈ C, dist x c ≤ ε := by
    intro x hx
    by_contra hcon
    push Not at hcon
    have hxC : x ∉ C := by
      intro hmem
      have h := hcon x hmem
      rw [dist_self] at h
      linarith
    have hCR' : ∀ c ∈ insert x C, ‖c‖ ≤ R := by
      intro c hc
      rw [Finset.mem_insert] at hc
      rcases hc with rfl | hc
      · exact hx
      · exact hCR c hc
    have hsep' : ((insert x C : Finset (EuclideanSpace ℝ (Fin m))) : Set (EuclideanSpace ℝ (Fin m))).Pairwise (fun c d => ε ≤ dist c d) := by
      intro a ha b hb hab
      show ε ≤ dist a b
      rw [Finset.coe_insert, Set.mem_insert_iff] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact le_of_lt (hcon b hb)
      · rw [dist_comm]
        exact le_of_lt (hcon a ha)
      · exact hsep ha hb hab
    have hcard' : (insert x C).card = k + 1 := by
      rw [Finset.card_insert_of_notMem hxC, hCcard]
    have hmem : k + 1 ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.zero_le _, ?_⟩, insert x C, hCR', hsep', hcard'⟩
      rw [← hcard']
      exact hcard _ hCR' hsep'
    have hle := hk_max (k + 1) hmem
    omega
  refine ⟨C, ?_, hcov, ?_⟩
  · intro x hx
    have h := hCR x hx
    linarith
  · exact vol C hCR hsep

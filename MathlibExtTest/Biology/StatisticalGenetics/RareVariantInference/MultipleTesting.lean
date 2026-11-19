/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.RareVariantInference.MultipleTesting

/-! # Tests for `MathlibExt.Biology.StatisticalGenetics.RareVariantInference.MultipleTesting`

* Smoke test: the two guarantees apply to an arbitrary tail-calibrated family.
* A concrete scan of three genes on the uniform probability space `[0, 1]`: two null genes whose
  statistics are perfectly correlated (PRDS but not independent) and one associated gene. The
  hypotheses are verified and the guarantees evaluate to `FDR ≤ 1/30` at `q = 1/20` and
  `P(FDP < 1/2) ≥ 9/10`. A single outcome where BH rejects all three genes shows the realized
  FDP (`2/3`) is not itself bounded by the FDR level.
* Boundary: a single null test on a fair coin whose reference tail understates the null tail
  (an uncorrected inflated statistic). Per-test validity fails, the p-value is not valid, and
  the FDR of BH at `q = 1/20` is `1/2 > q |H0| / m`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MultipleTesting
open MathlibExt.Biology.StatisticalGenetics.RareVariantInference.MultipleTesting

namespace MathlibExtTest.Biology.StatisticalGenetics.RareVariantInference.MultipleTesting

/-! ### Smoke test -/

/-- API-00 smoke test: both guarantees apply to any tail-calibrated family with PRDS
p-values. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ}
    (T : Fin m → Ω → ℝ) (G : Fin m → ℝ → ℝ) (H0 : Finset (Fin m))
    (h : IsTailCalibratedFamily μ T G H0) (hprds : IsPRDSOn μ (tailPValue T G) H0) :
    (∫ ω, falseDiscoveryProportion H0 (bhRejections (1 / 20) fun i => tailPValue T G i ω) ∂μ ≤
      1 / 20 * H0.card / m) ∧
    ENNReal.ofReal (1 - 1 / 10) ≤
      μ {ω | falseDiscoveryProportion H0 (bhRejections (1 / 20) fun i => tailPValue T G i ω) <
        1 / 20 / (1 / 10)} :=
  ⟨integral_fdp_bhRejections_tailPValue_le h hprds (by norm_num) (by norm_num),
    measure_fdp_bhRejections_tailPValue_lt_ge h hprds (by norm_num) (by norm_num) (by norm_num)⟩

/-! ### A concrete three-gene scan where the hypotheses hold -/

/-- The uniform law on `[0, 1]`. -/
noncomputable abbrev unif : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure unif := ⟨by simp [unif]⟩

/-- Gene statistics driven by one uniform draw `ω`: the two null genes `0, 1` share the
statistic `ω` (overlapping variant sets), the associated gene `2` has the shifted statistic
`(1 + ω) / 2`. -/
noncomputable def stat3 : Fin 3 → ℝ → ℝ := ![fun ω => ω, fun ω => ω, fun ω => (1 + ω) / 2]

/-- The reference upper tail `s ↦ 1 - s` for every gene: the exact null tail of a uniform
statistic on `[0, 1]`, extended linearly. -/
def tail3 : Fin 3 → ℝ → ℝ := fun _ s => 1 - s

/-- The null genes. -/
def nulls3 : Finset (Fin 3) := {0, 1}

/-- The uniform null tail is dominated by `1 - s`. -/
theorem unif_tail_le (s : ℝ) : unif {ω | s ≤ ω} ≤ ENNReal.ofReal (1 - s) := by
  rw [Measure.restrict_apply' measurableSet_Icc]
  calc volume ({ω : ℝ | s ≤ ω} ∩ Set.Icc 0 1) ≤ volume (Set.Icc s 1) :=
        measure_mono fun ω hω => ⟨hω.1, hω.2.2⟩
    _ = ENNReal.ofReal (1 - s) := Real.volume_Icc

/-- The three-gene scan is tail-calibrated. -/
theorem isTailCalibratedFamily_three : IsTailCalibratedFamily unif stat3 tail3 nulls3 where
  measurable_stat i := by
    fin_cases i
    · exact measurable_id
    · exact measurable_id
    · exact (measurable_const.add measurable_id).div_const _
  antitone_refTail _ := fun _ _ h => by simp only [tail3]; linarith
  null_tail_le i hi s := by
    simp only [nulls3, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact unif_tail_le s

/-- The p-value vector is a monotone function of either null p-value, hence PRDS on the nulls,
although the null p-values are perfectly dependent. -/
theorem isPRDSOn_three : IsPRDSOn unif (tailPValue stat3 tail3) nulls3 := by
  refine isPRDSOn_of_monotone_comp unif _ isTailCalibratedFamily_three.measurable_tailPValue
    nulls3 fun i hi => ⟨fun x => ![x, x, x / 2], fun x y hxy j => ?_, fun ω => ?_⟩
  · fin_cases j <;> simp <;> linarith
  · simp only [nulls3, Finset.mem_insert, Finset.mem_singleton] at hi
    funext j
    rcases hi with rfl | rfl <;> fin_cases j <;> simp [tailPValue, stat3, tail3] <;> ring

/-- The two null p-values are not independent: both equal `1 - ω`, so
`P(p₀ ≤ 1/2, p₁ ≤ 1/2) = 1/2 ≠ 1/4 = P(p₀ ≤ 1/2) P(p₁ ≤ 1/2)`. This is why the scan needs the
PRDS theorem rather than independence. -/
example : ¬ IndepFun (tailPValue stat3 tail3 0) (tailPValue stat3 tail3 1) unif := by
  intro h
  have h1 := h.measure_inter_preimage_eq_mul (Set.Iic (1 / 2 : ℝ)) (Set.Iic (1 / 2))
    measurableSet_Iic measurableSet_Iic
  have hpre (i : Fin 3) (hi : i = 0 ∨ i = 1) :
      tailPValue stat3 tail3 i ⁻¹' Set.Iic (1 / 2) = Set.Ici (1 / 2) := by
    rcases hi with rfl | rfl <;> ext ω <;>
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici, tailPValue, stat3, tail3] <;>
      norm_num <;> constructor <;> intro <;> linarith
  rw [hpre 0 (Or.inl rfl), hpre 1 (Or.inr rfl), Set.inter_self] at h1
  have hhalf : unif (Set.Ici (1 / 2)) = ENNReal.ofReal (1 / 2) := by
    have hI : Set.Ici (1 / 2 : ℝ) ∩ Set.Icc 0 1 = Set.Icc (1 / 2) 1 :=
      Set.ext fun x => ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, by linarith [h.1], h.2⟩⟩
    rw [Measure.restrict_apply measurableSet_Ici, hI, Real.volume_Icc]
    norm_num
  rw [hhalf, ← ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)] at h1
  norm_num at h1

/-- **FDR guarantee, computed.** BH at `q = 1/20` on the three-gene scan has FDR at most
`(1/20) · 2 / 3 = 1/30`. -/
example : ∫ ω, falseDiscoveryProportion nulls3
    (bhRejections (1 / 20) fun i => tailPValue stat3 tail3 i ω) ∂unif ≤ 1 / 30 := by
  refine (integral_fdp_bhRejections_tailPValue_le isTailCalibratedFamily_three isPRDSOn_three
    (by norm_num) (by norm_num)).trans_eq ?_
  simp [nulls3]
  norm_num

/-- **Uncertainty guarantee, computed.** With probability at least `9/10`, the gene set selected
by BH at `q = 1/20` has FDP below `1/2`. -/
example : ENNReal.ofReal (9 / 10) ≤ unif {ω | falseDiscoveryProportion nulls3
    (bhRejections (1 / 20) fun i => tailPValue stat3 tail3 i ω) < 1 / 2} := by
  have h := measure_fdp_bhRejections_tailPValue_lt_ge isTailCalibratedFamily_three isPRDSOn_three
    (q := 1 / 20) (δ := 1 / 10) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-- At the outcome `ω = 49/50` the p-values are `(1/50, 1/50, 1/100)`. -/
example : (fun i => tailPValue stat3 tail3 i (49 / 50)) = ![1 / 50, 1 / 50, 1 / 100] := by
  funext i
  fin_cases i <;> norm_num [tailPValue, stat3, tail3]

/-- At `p = (1/50, 1/50, 1/100)` BH at `q = 1/20` rejects all three genes, two of them null:
the realized FDP is `2/3`, far above the FDR bound `1/30`. -/
example : falseDiscoveryProportion nulls3 (bhRejections (1 / 20) ![1 / 50, 1 / 50, 1 / 100]) =
    2 / 3 := by
  have hidx : bhIndex (1 / 20) (![1 / 50, 1 / 50, 1 / 100] : Fin 3 → ℝ) = 3 := by
    refine le_antisymm (bhIndex_le _ _) (le_bhIndex le_rfl ?_)
    unfold numBelow
    rw [Finset.filter_true_of_mem fun i _ => by fin_cases i <;> norm_num]
    simp
  have hR : bhRejections (1 / 20) (![1 / 50, 1 / 50, 1 / 100] : Fin 3 → ℝ) = Finset.univ := by
    ext i
    fin_cases i <;> norm_num [bhRejections, hidx]
  rw [hR]
  norm_num [falseDiscoveryProportion, nulls3]

/-! ### Boundary: an anti-conservative null test -/

/-- A fair coin on `Bool`. -/
noncomputable abbrev coin : Measure Bool := (2⁻¹ : ENNReal) • Measure.count

instance : IsProbabilityMeasure coin :=
  ⟨by
    rw [Measure.smul_apply, Measure.count_univ, ENat.card_eq_coe_fintype_card, Fintype.card_bool]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

theorem coin_singleton (b : Bool) : coin {b} = 2⁻¹ := by simp [coin]

/-- One gene whose statistic is `10` or `0` with probability `1/2` each, under the null. -/
def statBad : Fin 1 → Bool → ℝ := fun _ b => if b then 10 else 0

/-- A reference tail claiming that a statistic of `10` has null tail probability `1/100`, while
under the actual null it has probability `1/2` (an inflated statistic read off an uncorrected
reference tail). -/
noncomputable def tailBad : Fin 1 → ℝ → ℝ := fun _ s => if 10 ≤ s then 1 / 100 else 1

/-- Per-test validity fails: the reference tail does not dominate the null tail. -/
example : ¬ IsTailCalibratedFamily coin statBad tailBad {0} := by
  intro h
  have h10 := h.null_tail_le 0 (by simp) 10
  have hset : {b : Bool | (10 : ℝ) ≤ statBad 0 b} = {true} := by
    ext b
    cases b <;> norm_num [statBad]
  rw [hset, coin_singleton] at h10
  norm_num [tailBad] at h10
  rw [ENNReal.le_ofReal_iff_toReal_le (by simp) (by norm_num)] at h10
  norm_num at h10

/-- The p-value is not valid: it is at most `1/100` with probability `1/2`. -/
example : ¬ IsValidPValue coin (tailPValue statBad tailBad 0) := by
  intro h
  have h1 := h (1 / 100) ⟨by norm_num, by norm_num⟩
  have hset : {b : Bool | tailPValue statBad tailBad 0 b ≤ 1 / 100} = {true} := by
    ext b
    cases b <;> norm_num [tailPValue, statBad, tailBad]
  rw [hset, coin_singleton, ENNReal.le_ofReal_iff_toReal_le (by simp) (by norm_num)] at h1
  norm_num at h1

/-- **The FDR guarantee fails.** BH at `q = 1/20` has FDR `1/2`, above `q |H0| / m = 1/20`. -/
example : ¬ ∫ b, falseDiscoveryProportion {0}
    (bhRejections (1 / 20) fun i => tailPValue statBad tailBad i b) ∂coin ≤
      1 / 20 * ({0} : Finset (Fin 1)).card / (1 : ℕ) := by
  have hrej_true : bhRejections (1 / 20) (fun i => tailPValue statBad tailBad i true) = {0} := by
    have hidx : bhIndex (1 / 20) (fun i => tailPValue statBad tailBad i true) = 1 := by
      refine le_antisymm (bhIndex_le _ _) (le_bhIndex le_rfl ?_)
      norm_num [numBelow, tailPValue, statBad, tailBad]
    ext i
    fin_cases i
    simp only [bhRejections, hidx]
    norm_num [tailPValue, statBad, tailBad]
  have hrej_false : bhRejections (1 / 20) (fun i => tailPValue statBad tailBad i false) = ∅ := by
    ext i
    fin_cases i
    have hk : (bhIndex (1 / 20) (fun i => tailPValue statBad tailBad i false) : ℝ) ≤ 1 := by
      exact_mod_cast bhIndex_le _ _
    simp only [bhRejections, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false, not_le]
    generalize (bhIndex (1 / 20) fun i => tailPValue statBad tailBad i false : ℝ) = k at hk ⊢
    norm_num [tailPValue, statBad, tailBad]
    linarith
  have hint : ∫ b, falseDiscoveryProportion {0}
      (bhRejections (1 / 20) fun i => tailPValue statBad tailBad i b) ∂coin = 1 / 2 := by
    rw [integral_fintype Integrable.of_finite]
    simp only [Fintype.sum_bool, hrej_true, hrej_false]
    simp [Measure.real, falseDiscoveryProportion]
  rw [hint]
  norm_num

end MathlibExtTest.Biology.StatisticalGenetics.RareVariantInference.MultipleTesting

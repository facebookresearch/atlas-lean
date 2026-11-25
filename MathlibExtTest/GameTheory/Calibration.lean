/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.Calibration

/-!
# Tests for asymptotic calibration

Closed checks of `calibrationScore` and `exists_calibrated_forecast`: the score of a calibrated
and of a miscalibrated sequence of forecasts; the score against Nature announcing rain exactly
when the forecast is at most `1/2` is at least `1/4`, whatever the forecasts; hence no
deterministic forecasting rule is `1/4`-calibrated (Oakes 1985; Dawid 1985), which is checked on a
one-point probability space, where every hypothesis of the theorem is discharged; and therefore
the rule given by the theorem for `ε = 1/4` is not deterministic.

## References

* D. Oakes, "Self-calibrating priors do not exist", J. Amer. Statist. Assoc. 80(390) (1985), 339.
* A. P. Dawid, "Comment" (on Oakes's paper), J. Amer. Statist. Assoc. 80(390) (1985), 340–341.
-/

open MeasureTheory Filter Finset
open MathlibExt.GameTheory.BlackwellApproachabilityWanted (historySigma)
open MathlibExt.GameTheory.CalibrationWanted

/-! ### The calibration score -/

/-- Forecasts `0, 1/2, 1/2, 1` for the outcomes `0, 1, 0, 1` are calibrated: score `0`. -/
example : calibrationScore (k := 2) (t := 4) ![0, 1, 1, 2] ![false, true, false, true] = 0 := by
  simp [calibrationScore, Fin.sum_univ_three, Finset.card_filter, Fin.sum_univ_four,
    -Finset.sum_boole]
  norm_num

/-- Forecasts `0, 0, 1` for the outcomes `1, 0, 0`: the forecast `0` has frequency `1/2` on two
of the three rounds and the forecast `1` frequency `0` on one, so the score is
`(1/2)² · 2/3 + 1² · 1/3 = 1/2`. -/
example : calibrationScore (k := 1) (t := 3) ![0, 0, 1] ![true, false, false] = 1 / 2 := by
  simp [calibrationScore, Fin.sum_univ_two, Finset.card_filter, Fin.sum_univ_three,
    -Finset.sum_boole]
  norm_num

/-- Against Nature announcing `1` exactly when the forecast is at most `1/2`, every forecast is
off by at least `1/2` on every round, so the calibration score is at least `1/4`. -/
private theorem quarter_le_calibrationScore {k t : ℕ} [NeZero k] [NeZero t]
    (f : Fin t → Fin (k + 1)) :
    1 / 4 ≤ calibrationScore f (fun s => decide (2 * (f s : ℕ) ≤ k)) := by
  have hk : (0 : ℝ) < k := Nat.cast_pos.2 (NeZero.pos k)
  have ht : (0 : ℝ) < t := Nat.cast_pos.2 (NeZero.pos t)
  have hterm : ∀ i : Fin (k + 1), (#{s | f s = i} : ℝ) / (4 * t) ≤
      ((#{s | f s = i ∧ decide (2 * (f s : ℕ) ≤ k) = true} : ℝ) / #{s | f s = i} -
        (i : ℝ) / k) ^ 2 * #{s | f s = i} / t := by
    intro i
    rw [div_le_div_iff₀ (by positivity) ht]
    by_cases hi : 2 * (i : ℕ) ≤ k
    · have hset : (univ.filter fun s => f s = i ∧ decide (2 * (f s : ℕ) ≤ k) = true) =
          univ.filter fun s => f s = i := by
        refine Finset.filter_congr fun s _ => ?_
        simp only [decide_eq_true_eq, and_iff_left_iff_imp]
        rintro rfl
        exact hi
      rw [hset]
      rcases Nat.eq_zero_or_pos #{s | f s = i} with h0 | hpos
      · simp [h0]
      have hn : (0 : ℝ) < #{s | f s = i} := by exact_mod_cast hpos
      rw [div_self hn.ne']
      have hik : (i : ℝ) / k ≤ 1 / 2 := by
        rw [div_le_iff₀ hk]
        have : (2 * (i : ℕ) : ℝ) ≤ k := by exact_mod_cast hi
        linarith
      have hik0 : 0 ≤ (i : ℝ) / k := by positivity
      have hp2 : 1 / 4 ≤ (1 - (i : ℝ) / k) ^ 2 := by nlinarith
      nlinarith [mul_nonneg hn.le ht.le]
    · have hset : (univ.filter fun s => f s = i ∧ decide (2 * (f s : ℕ) ≤ k) = true) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun s _ => ?_
        simp only [decide_eq_true_eq, not_and]
        rintro rfl
        exact hi
      rw [hset, card_empty, Nat.cast_zero, zero_div, zero_sub, neg_sq]
      have hik : 1 / 2 < (i : ℝ) / k := by
        rw [lt_div_iff₀ hk]
        have : (k : ℝ) < (2 * (i : ℕ) : ℝ) := by exact_mod_cast not_le.1 hi
        linarith
      have hn : (0 : ℝ) ≤ #{s | f s = i} := Nat.cast_nonneg _
      have hp2 : 1 / 4 ≤ ((i : ℝ) / k) ^ 2 := by nlinarith
      nlinarith [mul_nonneg hn ht.le]
  calc (1 : ℝ) / 4 = ∑ i : Fin (k + 1), (#{s | f s = i} : ℝ) / (4 * t) := by
        rw [← sum_div, ← Nat.cast_sum, ← card_eq_sum_card_fiberwise (fun s _ => mem_univ (f s)),
          card_univ, Fintype.card_fin]
        field_simp
    _ ≤ calibrationScore f (fun s => decide (2 * (f s : ℕ) ≤ k)) := sum_le_sum fun i _ => hterm i

/-! ### Deterministic rules are not calibrated -/

/-- The conclusion of `exists_calibrated_forecast` for a tolerance `ε`, a grid size `k` and a
forecasting rule `μ`. -/
private def IsCalibratedRule (ε : ℝ) (k : ℕ) [NeZero k]
    (μ : ∀ t : ℕ, (Fin t → Fin (k + 1) × Bool) → Convexity.StdSimplex ℝ (Fin (k + 1))) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → Fin (k + 1) × Bool), (∀ n z, MeasurableSet {ω | Z n ω = z}) →
    (∀ i b, P.real {ω | Z 0 ω = (i, b)} = (μ 0 Fin.elim0).weights i *
      P.real {ω | (Z 0 ω).2 = b}) →
    (∀ n i b,
      P[{ω | Z (n + 1) ω = (i, b)}.indicator (fun _ => (1 : ℝ)) | historySigma Z n] =ᵐ[P]
        fun ω => (μ (n + 1) (fun s => Z s ω)).weights i *
          P[{ω | (Z (n + 1) ω).2 = b}.indicator (fun _ => (1 : ℝ)) | historySigma Z n] ω) →
    ∀ᶠ t in atTop, 1 - ε < P.real {ω |
      calibrationScore (fun s : Fin (t + 1) => (Z s ω).1) (fun s => (Z s ω).2) < ε}

/-- The theorem, restated with `IsCalibratedRule`. -/
example {ε : ℝ} (hε : 0 < ε) : ∃ k : ℕ, ∃ _ : NeZero k, ∃ μ, IsCalibratedRule ε k μ :=
  exists_calibrated_forecast hε

/-- Nature's answer to a deterministic rule `g`: the rule forecasts `g n h` after the history `h`,
and Nature announces `1` exactly when that forecast is at most `1/2`. -/
private def natureSeq {k : ℕ} (g : ∀ t : ℕ, (Fin t → Fin (k + 1) × Bool) → Fin (k + 1)) :
    ℕ → Fin (k + 1) × Bool
  | n => (g n fun s => natureSeq g s, decide (2 * (g n fun s => natureSeq g s : ℕ) ≤ k))
termination_by n => n
decreasing_by all_goals exact s.isLt

private theorem natureSeq_eq {k : ℕ} (g : ∀ t : ℕ, (Fin t → Fin (k + 1) × Bool) → Fin (k + 1))
    (n : ℕ) : natureSeq g n =
      (g n fun s => natureSeq g s, decide (2 * (g n fun s => natureSeq g s : ℕ) ≤ k)) := by
  rw [natureSeq]

/-- On a one-point probability space every function is its own conditional expectation. -/
private theorem condExp_dirac_unit {α : Type} (Z : ℕ → Unit → α) (n : ℕ) (f : Unit → ℝ) :
    (Measure.dirac ())[f | historySigma Z n] = f := by
  have hf : f = fun _ => f () := funext fun u => by cases u; rfl
  rw [hf]
  exact condExp_const le_top (f ())

/-- **Deterministic rules are not calibrated** (Oakes 1985; Dawid 1985). No rule forecasting a
point of the grid, as a function of the history, is `1/4`-calibrated: on a one-point probability
space, Nature's sequence `natureSeq g` satisfies every hypothesis, and its calibration score is
at least `1/4` at every time. -/
private theorem not_isCalibratedRule_single {k : ℕ} [NeZero k]
    (g : ∀ t : ℕ, (Fin t → Fin (k + 1) × Bool) → Fin (k + 1)) :
    ¬ IsCalibratedRule (1 / 4) k fun t h => .single (g t h) := by
  intro h
  have h0 : (fun s : Fin 0 => natureSeq g s) = Fin.elim0 := funext fun s => s.elim0
  have hev := h (Measure.dirac ()) (fun n _ => natureSeq g n)
    (fun _ _ => (Set.toFinite _).measurableSet)
    (fun i b => by
      rw [natureSeq_eq, h0]
      by_cases hi : g 0 Fin.elim0 = i <;> cases b <;> simp [hi])
    (fun n i b => by
      rw [condExp_dirac_unit, condExp_dirac_unit]
      refine ae_of_all _ fun ω => ?_
      rw [natureSeq_eq g (n + 1)]
      by_cases hi : (g (n + 1) fun s => natureSeq g s) = i <;> cases b <;>
        simp [hi, Set.indicator])
  obtain ⟨t, ht⟩ := hev.exists
  have hscore : ∀ ω : Unit, ¬ calibrationScore (fun s : Fin (t + 1) => (natureSeq g s).1)
      (fun s => (natureSeq g s).2) < 1 / 4 := fun _ => by
    have hx : (fun s : Fin (t + 1) => (natureSeq g s).2) =
        fun s : Fin (t + 1) => decide (2 * ((natureSeq g s).1 : ℕ) ≤ k) := funext fun s => by
      rw [natureSeq_eq]
    rw [hx, not_lt]
    exact quarter_le_calibrationScore _
  rw [show {ω : Unit | calibrationScore (fun s : Fin (t + 1) => (natureSeq g s).1)
      (fun s => (natureSeq g s).2) < 1 / 4} = ∅ from Set.eq_empty_iff_forall_notMem.2 hscore,
    measureReal_empty] at ht
  norm_num at ht

/-- The rule given by `exists_calibrated_forecast` for `ε = 1/4` is randomised: it is not of the
form `t h ↦ δ_{g t h}`. -/
example : ∃ k : ℕ, ∃ _ : NeZero k, ∃ μ, IsCalibratedRule (1 / 4) k μ ∧
    ∀ g : ∀ t : ℕ, (Fin t → Fin (k + 1) × Bool) → Fin (k + 1), μ ≠ fun t h => .single (g t h) := by
  obtain ⟨k, hk, μ, hμ⟩ := exists_calibrated_forecast (ε := 1 / 4) (by norm_num)
  refine ⟨k, hk, μ, hμ, fun g hg => not_isCalibratedRule_single g ?_⟩
  rw [← hg]
  exact hμ

#print axioms exists_calibrated_forecast

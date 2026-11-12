/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Basic
public import Mathlib.Probability.UniformOn

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.Basic

/-- Three p-values `0.01, 0.02, 0.5`. -/
noncomputable def p3 : Fin 3 → ℝ := ![1 / 100, 2 / 100, 1 / 2]

/-- Two of the three p-values are at most `0.025`. -/
theorem numBelow_p3 : numBelow p3 (1 / 40) = 2 := by
  rw [numBelow, show (Finset.univ.filter fun i => p3 i ≤ 1 / 40) = {0, 1} by
    ext i; fin_cases i <;> norm_num [p3]]
  rfl

/-- Boundary: a threshold below every p-value counts nothing; `1` counts everything. -/
example : numBelow p3 0 = 0 := by
  rw [numBelow, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  fin_cases i <;> norm_num [p3]

example : numBelow p3 1 = 3 := by
  rw [numBelow, Finset.filter_true_of_mem fun i _ => by fin_cases i <;> norm_num [p3]]
  rfl

/-- Non-vacuity of `IsValidPValue`: the identity on `[0, 1]` under Lebesgue measure is a
uniform, hence valid, p-value. -/
example : IsValidPValue (volume.restrict (Set.Icc (0 : ℝ) 1)) id :=
  isValidPValue_of_hasLaw_uniform HasLaw.id

/-- A constant p-value `1` is valid (it is conservative), under a Dirac measure. -/
example : IsValidPValue (Measure.dirac ()) fun _ : Unit => (1 : ℝ) := by
  intro t ht
  rcases eq_or_lt_of_le ht.2 with rfl | hlt
  · simp
  · simp [not_le.2 hlt]

/-- Two bits `ω = (a, b)` under the uniform measure on `Fin 2 × Fin 2`, conditioned on `a = t`:
the event `b = t` has probability `1/2`. -/
theorem cond_snd_eq_fst (t : ℕ) (ht : t ≤ 1) :
    (uniformOn (Set.univ : Set (Fin 2 × Fin 2)))[{ω | (ω.2 : ℕ) = t} |
      (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ)) ⁻¹' {t}] = 1 / 2 := by
  have hA : Set.univ ∩ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ)) ⁻¹' {t} =
      ↑(Finset.univ.filter fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = t) := by
    ext ω; simp
  have hB : {ω : Fin 2 × Fin 2 | (ω.2 : ℕ) = t} =
      ↑(Finset.univ.filter fun ω : Fin 2 × Fin 2 => (ω.2 : ℕ) = t) := by
    ext ω; simp
  have h₁ : ((Finset.univ.filter fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = t) ∩
      Finset.univ.filter fun ω : Fin 2 × Fin 2 => (ω.2 : ℕ) = t).card = 1 := by
    interval_cases t <;> decide
  have h₂ : (Finset.univ.filter fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = t).card = 2 := by
    interval_cases t <;> decide
  rw [uniformOn, cond_cond_eq_cond_inter .of_discrete .of_discrete, ← uniformOn, hA, hB,
    uniformOn_apply_finset, h₁, h₂]
  norm_num

/-- **Validity by averaging over a two-valued count.** Under the uniform measure on two bits
`ω = (a, b)`, the count `S = a` takes the values `0` and `1`, and the p-value is
`q a ω = 1/2` if `b = a` and `1` otherwise, so it depends on the value of `S`. Each `q t` is valid
given `S = t` (the event `b = t` has conditional probability `1/2`), so the averaged p-value
`P ω = q (S ω) ω` is valid under the uniform measure. -/
example : IsValidPValue (uniformOn (Set.univ : Set (Fin 2 × Fin 2)))
    fun ω => if (ω.2 : ℕ) = ω.1 then (1 / 2 : ℝ) else 1 := by
  refine isValidPValue_of_forall_cond (S := fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ)) .of_discrete
    (N := 1) (ae_of_all _ fun ω => Nat.lt_succ_iff.1 ω.1.isLt)
    (q := fun t ω => if (ω.2 : ℕ) = t then (1 / 2 : ℝ) else 1) (fun _ _ => rfl)
    fun t ht s hs => ?_
  beta_reduce
  rcases lt_or_ge s (1 / 2) with hs₁ | hs₁
  · have : {ω : Fin 2 × Fin 2 | (if (ω.2 : ℕ) = t then (1 / 2 : ℝ) else 1) ≤ s} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      split_ifs <;> linarith
    rw [this, measure_empty]
    exact zero_le
  rcases lt_or_ge s 1 with hs₂ | hs₂
  · have : {ω : Fin 2 × Fin 2 | (if (ω.2 : ℕ) = t then (1 / 2 : ℝ) else 1) ≤ s} =
        {ω | (ω.2 : ℕ) = t} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      split_ifs with h
      · exact iff_of_true hs₁ h
      · exact iff_of_false (by linarith) h
    rw [this, cond_snd_eq_fst t ht, show (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2) by
      rw [ENNReal.ofReal_div_of_pos two_pos]; simp]
    exact ENNReal.ofReal_le_ofReal hs₁
  · calc _ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal s := by rw [le_antisymm hs.2 hs₂, ENNReal.ofReal_one]

/-- False discovery proportion: rejecting `{0, 1}` with `H0 = {1, 2}` gives `1 / 2`; rejecting
nothing gives `0`. -/
example : falseDiscoveryProportion ({1, 2} : Finset (Fin 3)) {0, 1} = 1 / 2 := by
  norm_num [falseDiscoveryProportion]

example (H0 : Finset (Fin 3)) : falseDiscoveryProportion H0 ∅ = 0 := by
  simp [falseDiscoveryProportion]

example (H0 R : Finset (Fin 3)) :
    0 ≤ falseDiscoveryProportion H0 R ∧ falseDiscoveryProportion H0 R ≤ 1 :=
  ⟨falseDiscoveryProportion_nonneg H0 R, falseDiscoveryProportion_le_one H0 R⟩

/-- Use: outward translation by `ε ≥ 0` stays valid. -/
example {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {p : Ω → ℝ} (hp : IsValidPValue μ p) {ε : ℝ} (hε : 0 ≤ ε) :
    IsValidPValue μ (fun ω => p ω + ε) := by
  exact hp.mono_ae (Filter.Eventually.of_forall fun ω => le_add_of_nonneg_right hε)

/-- Use: capping a p-value bounded above by `1` (at most `1` a.e.) at `1` stays valid. -/
example {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {p : Ω → ℝ} (hp : IsValidPValue μ p) {ε : ℝ} (hε : 0 ≤ ε)
    (hle : ∀ᵐ ω ∂μ, p ω ≤ 1) :
    IsValidPValue μ (fun ω => min 1 (p ω + ε)) := by
  apply hp.mono_ae
  filter_upwards [hle] with ω hω
  exact le_min hω (le_add_of_nonneg_right hε)

/-- Use: the constant `1` function is a valid p-value under any probability law. -/
example (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsValidPValue μ (fun _ => (1 : ℝ)) := by
  intro t ht
  by_cases h : (1 : ℝ) ≤ t
  · have ht1 : t = 1 := le_antisymm ht.2 h
    subst ht1
    have hset : {ω : ℝ | (fun _ => (1 : ℝ)) ω ≤ 1} = Set.univ :=
      Set.eq_univ_of_forall fun _ => show (1 : ℝ) ≤ 1 from le_refl 1
    rw [hset, IsProbabilityMeasure.measure_univ, ENNReal.ofReal_one]
  · have hset : {ω : ℝ | (fun _ => (1 : ℝ)) ω ≤ t} = ∅ :=
      Set.eq_empty_of_forall_notMem fun _ => h
    rw [hset, measure_empty]
    exact zero_le

/-- Negative: rounding down breaks validity (constant `1` rounded to `1 / 2` fails at `t = 3 / 4`). -/
example (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ¬ IsValidPValue μ (fun _ : ℝ => (1 - 1 / 2 : ℝ)) := by
  intro hcon
  have h34 := hcon (3 / 4 : ℝ) ⟨by norm_num, by norm_num⟩
  have hset : {ω : ℝ | (fun _ : ℝ => (1 - 1 / 2 : ℝ)) ω ≤ 3 / 4} = Set.univ :=
    Set.eq_univ_of_forall fun _ => show (1 - 1 / 2 : ℝ) ≤ 3 / 4 by norm_num
  rw [hset, IsProbabilityMeasure.measure_univ] at h34
  have hlt : ENNReal.ofReal (3 / 4 : ℝ) < 1 :=
    ENNReal.ofReal_lt_one.mpr (by norm_num)
  exact (not_le_of_gt hlt) h34

end MathlibExtTest.Probability.Statistics.MultipleTesting.Basic

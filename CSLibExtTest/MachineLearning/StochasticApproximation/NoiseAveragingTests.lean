/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.StochasticApproximation.NoiseAveraging
import Mathlib.Analysis.PSeries

/-!
# Tests for noise averaging in stochastic approximation

Boundary probes for `ae_tendsto_zero` (Tsitsiklis 1994, Lemma 1). Each negative control keeps all
hypotheses but one, adds the initial value `W 0 = 0` and the source's nonnegative envelope
`0 ≤ B t`, and asserts that the conclusion then fails on an explicit model, so the dropped
hypothesis cannot be removed even in the source's setting:

* `lemma1_needs_divergence` drops (d), the divergence of the step sums. Model: a fair coin,
  `ℱ 0` trivial and `ℱ t` everything for `t ≥ 1`, one noisy step `α 0 = 1 / 2` with
  `w 0 = ±1`, then `α t = w t = 0`, and `B = 1`; then `W t = ±1 / 2` for every `t ≥ 1`.
* `lemma1_needs_centering` drops the centering condition (a) and keeps the conditional second
  moment bound (b). Model: one point, `w = 1`, `B = 1` and `α t = 1 / (t + 1)`; then `W t = 1`
  for every `t ≥ 1`.

The positive control `ae_tendsto_zero_hypotheses_satisfiable` shows that the hypotheses of
`ae_tendsto_zero` hold together for noise that is not almost surely zero, and
`restart_coin_tendsto_zero` applies the lemma to that model. `isCenteredNoise_neg_one_iff` pins
how the contract reads a negative envelope. Three examples show what the contract allows outside
the setting where its fields are conditional moments: every `w` satisfies it when `m` is not a
sub-σ-algebra or `μ.trim` is not σ-finite, and, on `Bool` with the trivial σ-algebra, a
nonnegative `w` that is not a.e.-measurable satisfies it with envelope `0` without being almost
everywhere `0`. The remaining examples apply the bridges and the lemmas in the shapes their
consumers use.
-/

@[expose] public section

namespace Cslib.MachineLearning.NoiseAveragingTests

open MeasureTheory Filter Topology
open scoped ENNReal
open Cslib.MachineLearning.StochasticApproximation.NoiseAveraging

/-! ### Negative controls -/

private noncomputable def nsa_aux_s5_μ : Measure[⊤] (Fin 2) :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac 0 + Measure.dirac 1)

private theorem nsa_aux_s5_add_apply (μ ν : Measure[⊤] (Fin 2)) (s : Set (Fin 2)) :
    (μ + ν) s = μ s + ν s := rfl

private theorem nsa_aux_s5_smul_apply (c : ℝ≥0∞) (μ : Measure[⊤] (Fin 2)) (s : Set (Fin 2)) :
    (c • μ) s = c • μ s := rfl

private theorem nsa_aux_s5_μ_univ : nsa_aux_s5_μ Set.univ = 1 := by
  unfold nsa_aux_s5_μ
  rw [nsa_aux_s5_smul_apply, nsa_aux_s5_add_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, one_add_one_eq_two]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

private instance nsa_aux_s5_prob : IsProbabilityMeasure nsa_aux_s5_μ := ⟨nsa_aux_s5_μ_univ⟩

private noncomputable def nsa_aux_s5_ℱ : Filtration ℕ (⊤ : MeasurableSpace (Fin 2)) :=
  { seq := fun n => match n with | 0 => ⊥ | _ + 1 => ⊤
    mono' := by
      intro a b hab
      cases a with
      | zero => exact bot_le
      | succ a =>
        cases b with
        | zero => exact (by omega : False).elim
        | succ b => exact le_rfl
    le' := fun _ => le_top }

private theorem nsa_aux_s5_F_zero : nsa_aux_s5_ℱ 0 = ⊥ := rfl

private theorem nsa_aux_s5_F_succ (t : ℕ) : nsa_aux_s5_ℱ (t + 1) = ⊤ := rfl

private noncomputable def nsa_aux_s5_Fbot : Filtration ℕ (⊤ : MeasurableSpace (Fin 2)) :=
  { seq := fun _ => ⊥
    mono' := fun _ _ _ => le_rfl
    le' := fun _ => bot_le }

private theorem nsa_aux_s5_Fbot_eq (t : ℕ) : nsa_aux_s5_Fbot t = ⊥ := rfl

private def nsa_aux_s5_w0 : Fin 2 → ℝ := fun ω => if ω = 0 then 1 else -1

private theorem nsa_aux_s5_w0_zero : nsa_aux_s5_w0 0 = 1 := by
  show (if (0 : Fin 2) = 0 then (1 : ℝ) else -1) = 1
  exact ite_eq_left rfl

private theorem nsa_aux_s5_w0_one : nsa_aux_s5_w0 1 = -1 := by
  show (if (1 : Fin 2) = 0 then (1 : ℝ) else -1) = -1
  exact ite_eq_right (by decide)

private theorem nsa_aux_s5_w0_sq (ω : Fin 2) : nsa_aux_s5_w0 ω ^ 2 = 1 := by
  by_cases h : ω = 0
  · subst h
    rw [nsa_aux_s5_w0_zero]
    norm_num
  · have hw : nsa_aux_s5_w0 ω = -1 := by
      show (if ω = 0 then (1 : ℝ) else -1) = -1
      exact ite_eq_right h
    rw [hw]
    norm_num

private theorem nsa_aux_s5_lintegral_eq (X : Fin 2 → ℝ≥0∞) :
    ∫⁻ ω, X ω ∂nsa_aux_s5_μ = (2⁻¹ : ℝ≥0∞) • (X 0 + X 1) := by
  unfold nsa_aux_s5_μ
  rw [lintegral_smul_measure, lintegral_add_measure, lintegral_dirac, lintegral_dirac]

private theorem nsa_aux_s5_lintegral_sq :
    ∫⁻ ω, ENNReal.ofReal (nsa_aux_s5_w0 ω ^ 2) ∂nsa_aux_s5_μ = 1 := by
  rw [nsa_aux_s5_lintegral_eq]
  show (2⁻¹ : ℝ≥0∞) •
    (ENNReal.ofReal (nsa_aux_s5_w0 0 ^ 2) + ENNReal.ofReal (nsa_aux_s5_w0 1 ^ 2)) = 1
  simp only [nsa_aux_s5_w0_sq, ENNReal.ofReal_one]
  rw [smul_eq_mul, one_add_one_eq_two]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

private theorem nsa_aux_s5_lintegral_pos :
    ∫⁻ ω, ENNReal.ofReal (nsa_aux_s5_w0 ω) ∂nsa_aux_s5_μ = 2⁻¹ := by
  rw [nsa_aux_s5_lintegral_eq]
  show (2⁻¹ : ℝ≥0∞) • (ENNReal.ofReal (nsa_aux_s5_w0 0) + ENNReal.ofReal (nsa_aux_s5_w0 1)) = 2⁻¹
  rw [nsa_aux_s5_w0_zero, nsa_aux_s5_w0_one, ENNReal.ofReal_one]
  have hneg : ENNReal.ofReal (-1 : ℝ) = 0 := by simp
  rw [hneg, add_zero, smul_eq_mul, mul_one]

private theorem nsa_aux_s5_lintegral_neg :
    ∫⁻ ω, ENNReal.ofReal (-nsa_aux_s5_w0 ω) ∂nsa_aux_s5_μ = 2⁻¹ := by
  rw [nsa_aux_s5_lintegral_eq]
  show (2⁻¹ : ℝ≥0∞) • (ENNReal.ofReal (-nsa_aux_s5_w0 0) + ENNReal.ofReal (-nsa_aux_s5_w0 1)) = 2⁻¹
  rw [nsa_aux_s5_w0_zero, nsa_aux_s5_w0_one]
  have hneg : ENNReal.ofReal (-1 : ℝ) = 0 := by simp
  rw [hneg, neg_neg, ENNReal.ofReal_one, zero_add, smul_eq_mul, mul_one]

private theorem nsa_aux_s5_centered_zero :
    IsCenteredNoise (nsa_aux_s5_ℱ 0) nsa_aux_s5_μ nsa_aux_s5_w0 (fun _ => 1) := by
  rw [nsa_aux_s5_F_zero]
  constructor
  · have hbot := condLExp_bot_ae_eq nsa_aux_s5_μ
      (fun ω => ENNReal.ofReal (nsa_aux_s5_w0 ω ^ 2))
    rw [nsa_aux_s5_μ_univ, nsa_aux_s5_lintegral_sq] at hbot
    simp only [inv_one, one_smul] at hbot
    filter_upwards [hbot] with ω hω
    simp [hω, ENNReal.ofReal_one]
  · have h1 := condLExp_bot_ae_eq nsa_aux_s5_μ
      (fun ω => ENNReal.ofReal (nsa_aux_s5_w0 ω))
    have h2 := condLExp_bot_ae_eq nsa_aux_s5_μ
      (fun ω => ENNReal.ofReal (-nsa_aux_s5_w0 ω))
    rw [nsa_aux_s5_μ_univ, nsa_aux_s5_lintegral_pos] at h1
    rw [nsa_aux_s5_μ_univ, nsa_aux_s5_lintegral_neg] at h2
    simp only [inv_one, one_smul] at h1 h2
    exact h1.trans h2.symm

private theorem nsa_aux_s5_centered_const_zero (m : MeasurableSpace (Fin 2)) :
    IsCenteredNoise m nsa_aux_s5_μ (fun _ => 0) (fun _ => 1) := by
  constructor
  · have h0 : (fun ω : Fin 2 => ENNReal.ofReal ((fun _ => (0 : ℝ)) ω ^ 2)) =ᵐ[nsa_aux_s5_μ] 0 :=
      Eventually.of_forall fun ω => by simp
    have hc := condLExp_congr_ae (mΩ := m) h0
    rw [condLExp_zero] at hc
    filter_upwards [hc] with ω hω
    rw [hω]
    show (0 : ℝ≥0∞) ≤ ENNReal.ofReal 1
    rw [ENNReal.ofReal_one]
    exact zero_le_one
  · have hpos : (fun ω : Fin 2 => ENNReal.ofReal ((fun _ => (0 : ℝ)) ω)) =ᵐ[nsa_aux_s5_μ] 0 :=
      Eventually.of_forall fun ω => by simp
    have hneg : (fun ω : Fin 2 => ENNReal.ofReal (-(fun _ => (0 : ℝ)) ω)) =ᵐ[nsa_aux_s5_μ] 0 :=
      Eventually.of_forall fun ω => by simp
    have hc1 := condLExp_congr_ae (mΩ := m) hpos
    have hc2 := condLExp_congr_ae (mΩ := m) hneg
    rw [condLExp_zero] at hc1 hc2
    exact hc1.trans hc2.symm

private def nsa_aux_s5_B : ℕ → Fin 2 → ℝ := fun _ _ => 1

private theorem nsa_aux_s5_B_nonneg : ∀ᵐ ω ∂nsa_aux_s5_μ, ∀ t, 0 ≤ nsa_aux_s5_B t ω :=
  Eventually.of_forall fun _ _ => zero_le_one

private theorem nsa_aux_s5_B_bdd :
    ∀ᵐ ω ∂nsa_aux_s5_μ, BddAbove (Set.range fun t => nsa_aux_s5_B t ω) := by
  refine Eventually.of_forall fun ω => ?_
  exact ⟨1, fun y hy => by
    obtain ⟨t, ht⟩ := hy
    rw [← ht]
    show (1 : ℝ) ≤ 1
    exact le_rfl⟩

private theorem nsa_aux_s5_ae_false_of_pointwise {P : Fin 2 → Prop} (hconc : ∀ᵐ ω ∂nsa_aux_s5_μ, P ω)
    (hneg : ∀ ω, ¬ P ω) : False := by
  have hfalse : ∀ᵐ ω ∂nsa_aux_s5_μ, False := by
    filter_upwards [hconc] with ω hω
    exact (hneg ω) hω
  have hmem : {ω : Fin 2 | False} ∈ ae nsa_aux_s5_μ := hfalse
  rw [mem_ae_iff] at hmem
  have hun : {ω : Fin 2 | False}ᶜ = Set.univ := by
    ext ω
    simp
  rw [hun, nsa_aux_s5_μ_univ] at hmem
  exact one_ne_zero hmem

private noncomputable def nsa_aux_s5_a1 : ℕ → Fin 2 → ℝ := fun t _ => if t = 0 then 1 / 2 else 0

private theorem nsa_aux_s5_a1_zero (ω : Fin 2) : nsa_aux_s5_a1 0 ω = 1 / 2 := by
  show (if (0 : ℕ) = 0 then (1 / 2 : ℝ) else 0) = 1 / 2
  exact ite_eq_left rfl

private theorem nsa_aux_s5_a1_succ (t : ℕ) (ω : Fin 2) : nsa_aux_s5_a1 (t + 1) ω = 0 := by
  show (if t + 1 = 0 then (1 / 2 : ℝ) else 0) = 0
  exact ite_eq_right (by omega)

private theorem nsa_aux_s5_a1_sq_le (n : ℕ) (ω : Fin 2) :
    ∑ t ∈ Finset.range n, nsa_aux_s5_a1 t ω ^ 2 ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases hn : n = 0
    · subst hn
      rw [Finset.sum_range_zero, nsa_aux_s5_a1_zero]
      norm_num
    · have hn1 : nsa_aux_s5_a1 n ω = 0 := by
        obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        exact nsa_aux_s5_a1_succ n' ω
      rw [hn1]
      have hz : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [hz, add_zero]
      exact ih

private def nsa_aux_s5_w1 : ℕ → Fin 2 → ℝ := fun t ω => if t = 0 then nsa_aux_s5_w0 ω else 0

private theorem nsa_aux_s5_w1_zero (ω : Fin 2) : nsa_aux_s5_w1 0 ω = nsa_aux_s5_w0 ω := by
  show (if (0 : ℕ) = 0 then nsa_aux_s5_w0 ω else 0) = nsa_aux_s5_w0 ω
  exact ite_eq_left rfl

private theorem nsa_aux_s5_w1_succ (t : ℕ) (ω : Fin 2) : nsa_aux_s5_w1 (t + 1) ω = 0 := by
  show (if t + 1 = 0 then nsa_aux_s5_w0 ω else 0) = 0
  exact ite_eq_right (by omega)

private theorem nsa_aux_s5_w1_zero_fun : nsa_aux_s5_w1 0 = nsa_aux_s5_w0 := by
  ext ω
  exact nsa_aux_s5_w1_zero ω

private theorem nsa_aux_s5_w1_succ_fun (t : ℕ) : nsa_aux_s5_w1 (t + 1) = fun _ => 0 := by
  ext ω
  exact nsa_aux_s5_w1_succ t ω

private theorem nsa_aux_s5_w1_meas (t : ℕ) :
    StronglyMeasurable[nsa_aux_s5_ℱ (t + 1)] (nsa_aux_s5_w1 t) := by
  rw [nsa_aux_s5_F_succ]
  exact Measurable.stronglyMeasurable (fun _ _ => trivial)

private theorem nsa_aux_s5_w1_centered (t : ℕ) :
    IsCenteredNoise (nsa_aux_s5_ℱ t) nsa_aux_s5_μ (nsa_aux_s5_w1 t) (nsa_aux_s5_B t) := by
  cases t with
  | zero =>
    rw [nsa_aux_s5_w1_zero_fun]
    exact nsa_aux_s5_centered_zero
  | succ t =>
    rw [nsa_aux_s5_w1_succ_fun, nsa_aux_s5_F_succ]
    exact nsa_aux_s5_centered_const_zero _

private noncomputable def nsa_aux_s5_W1 : ℕ → Fin 2 → ℝ :=
  fun t ω => if t = 0 then 0 else nsa_aux_s5_w0 ω / 2

private theorem nsa_aux_s5_W1_zero (ω : Fin 2) : nsa_aux_s5_W1 0 ω = 0 := by
  show (if (0 : ℕ) = 0 then (0 : ℝ) else nsa_aux_s5_w0 ω / 2) = 0
  exact ite_eq_left rfl

private theorem nsa_aux_s5_W1_succ (t : ℕ) (ω : Fin 2) :
    nsa_aux_s5_W1 (t + 1) ω = nsa_aux_s5_w0 ω / 2 := by
  show (if t + 1 = 0 then (0 : ℝ) else nsa_aux_s5_w0 ω / 2) = nsa_aux_s5_w0 ω / 2
  exact ite_eq_right (by omega)

private theorem nsa_aux_s5_W1_of_ge_one {t : ℕ} (ht : 1 ≤ t) (ω : Fin 2) :
    nsa_aux_s5_W1 t ω = nsa_aux_s5_w0 ω / 2 := by
  obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  exact nsa_aux_s5_W1_succ t' ω

private theorem nsa_aux_s5_W1_not_tendsto (ω : Fin 2) :
    ¬ Tendsto (fun t => nsa_aux_s5_W1 t ω) atTop (𝓝 0) := by
  intro h0
  have heq : (fun _ => nsa_aux_s5_w0 ω / 2) =ᶠ[atTop] (fun t => nsa_aux_s5_W1 t ω) := by
    show ∀ᶠ t in atTop, nsa_aux_s5_w0 ω / 2 = nsa_aux_s5_W1 t ω
    rw [eventually_atTop]
    exact ⟨1, fun t ht => (nsa_aux_s5_W1_of_ge_one ht ω).symm⟩
  have hlim := Tendsto.congr' heq tendsto_const_nhds
  have huniq := tendsto_nhds_unique hlim h0
  have hsq := nsa_aux_s5_w0_sq ω
  have hw0 : nsa_aux_s5_w0 ω = 0 := by linarith [huniq]
  rw [hw0] at hsq
  norm_num at hsq

private noncomputable def nsa_aux_s5_a2 : ℕ → Fin 2 → ℝ := fun t _ => 1 / ((t : ℝ) + 1)

private theorem nsa_aux_s5_ha2 (t : ℕ) (ω : Fin 2) : nsa_aux_s5_a2 t ω = 1 / ((t : ℝ) + 1) := rfl

private theorem nsa_aux_s5_a2_zero (ω : Fin 2) : nsa_aux_s5_a2 0 ω = 1 := by
  rw [nsa_aux_s5_ha2]
  simp

private theorem nsa_aux_s5_a2_mem (t : ℕ) (ω : Fin 2) : nsa_aux_s5_a2 t ω ∈ Set.Icc (0 : ℝ) 1 := by
  rw [nsa_aux_s5_ha2, Set.mem_Icc]
  constructor
  · exact div_nonneg zero_le_one (by positivity)
  · rw [div_le_one (by positivity : (0 : ℝ) < (t : ℝ) + 1)]
    have hn : (0 : ℝ) ≤ (t : ℝ) := by positivity
    linarith

private theorem nsa_aux_s5_a2_div (ω : Fin 2) :
    Tendsto (fun n => ∑ t ∈ Finset.range n, nsa_aux_s5_a2 t ω) atTop atTop := by
  simp only [nsa_aux_s5_ha2]
  exact Real.tendsto_sum_range_one_div_nat_succ_atTop

private theorem nsa_aux_s5_a2_sq_step (n : ℕ) :
    ((1 : ℝ) / ((n : ℝ) + 1)) ^ 2 ≤ 2 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 2) := by
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  field_simp
  ring_nf
  linarith

private theorem nsa_aux_s5_a2_sq_le_aux (n : ℕ) :
    ∑ t ∈ Finset.range n, ((1 : ℝ) / ((t : ℝ) + 1)) ^ 2 ≤ 2 - 2 / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    calc ∑ t ∈ Finset.range n, ((1 : ℝ) / ((t : ℝ) + 1)) ^ 2 + ((1 : ℝ) / ((n : ℝ) + 1)) ^ 2
        ≤ (2 - 2 / ((n : ℝ) + 1)) + (2 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 2)) :=
          add_le_add ih (nsa_aux_s5_a2_sq_step n)
      _ = 2 - 2 / ((n : ℝ) + 1 + 1) := by ring

private theorem nsa_aux_s5_a2_sq_le (n : ℕ) (ω : Fin 2) :
    ∑ t ∈ Finset.range n, nsa_aux_s5_a2 t ω ^ 2 ≤ 2 := by
  have h := nsa_aux_s5_a2_sq_le_aux n
  have h2 : (2 : ℝ) - 2 / ((n : ℝ) + 1) ≤ 2 := by
    have hpos : (0 : ℝ) ≤ 2 / ((n : ℝ) + 1) := by positivity
    linarith
  simp only [nsa_aux_s5_ha2]
  exact le_trans h h2

private def nsa_aux_s5_w2 : ℕ → Fin 2 → ℝ := fun _ _ => 1

private theorem nsa_aux_s5_var_one (t : ℕ) :
    nsa_aux_s5_μ⁻[fun ω => ENNReal.ofReal (nsa_aux_s5_w2 t ω ^ 2) | nsa_aux_s5_Fbot t]
      ≤ᵐ[nsa_aux_s5_μ] fun ω => ENNReal.ofReal (nsa_aux_s5_B t ω) := by
  rw [nsa_aux_s5_Fbot_eq]
  have hbot := condLExp_bot_ae_eq nsa_aux_s5_μ
    (fun ω => ENNReal.ofReal (nsa_aux_s5_w2 t ω ^ 2))
  have hint : ∫⁻ ω, ENNReal.ofReal (nsa_aux_s5_w2 t ω ^ 2) ∂nsa_aux_s5_μ = 1 := by
    rw [nsa_aux_s5_lintegral_eq]
    show (2⁻¹ : ℝ≥0∞) •
      (ENNReal.ofReal (nsa_aux_s5_w2 t 0 ^ 2) + ENNReal.ofReal (nsa_aux_s5_w2 t 1 ^ 2)) = 1
    have e0 : nsa_aux_s5_w2 t 0 = 1 := rfl
    have e1 : nsa_aux_s5_w2 t 1 = 1 := rfl
    have ho : (1 : ℝ) ^ 2 = 1 := by norm_num
    rw [e0, e1, ho, ENNReal.ofReal_one, smul_eq_mul, one_add_one_eq_two]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  rw [nsa_aux_s5_μ_univ, hint] at hbot
  simp only [inv_one, one_smul] at hbot
  filter_upwards [hbot] with ω hω
  simp [hω, nsa_aux_s5_B, ENNReal.ofReal_one]

private def nsa_aux_s5_W2 : ℕ → Fin 2 → ℝ := fun t _ => if t = 0 then 0 else 1

private theorem nsa_aux_s5_W2_zero (ω : Fin 2) : nsa_aux_s5_W2 0 ω = 0 := by
  show (if (0 : ℕ) = 0 then (0 : ℝ) else 1) = 0
  exact ite_eq_left rfl

private theorem nsa_aux_s5_W2_succ (t : ℕ) (ω : Fin 2) : nsa_aux_s5_W2 (t + 1) ω = 1 := by
  show (if t + 1 = 0 then (0 : ℝ) else 1) = 1
  exact ite_eq_right (by omega)

private theorem nsa_aux_s5_W2_of_ge_one {t : ℕ} (ht : 1 ≤ t) (ω : Fin 2) :
    nsa_aux_s5_W2 t ω = 1 := by
  obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  exact nsa_aux_s5_W2_succ t' ω

private theorem nsa_aux_s5_W2_not_tendsto (ω : Fin 2) :
    ¬ Tendsto (fun t => nsa_aux_s5_W2 t ω) atTop (𝓝 0) := by
  intro h0
  have heq : (fun _ => (1 : ℝ)) =ᶠ[atTop] (fun t => nsa_aux_s5_W2 t ω) := by
    show ∀ᶠ t in atTop, (1 : ℝ) = nsa_aux_s5_W2 t ω
    rw [eventually_atTop]
    exact ⟨1, fun t ht => (nsa_aux_s5_W2_of_ge_one ht ω).symm⟩
  have hlim := Tendsto.congr' heq tendsto_const_nhds
  have huniq := tendsto_nhds_unique hlim h0
  norm_num at huniq

private theorem nsa_aux_s5_w1_not_ae_zero : ¬ nsa_aux_s5_w1 0 =ᵐ[nsa_aux_s5_μ] 0 := by
  rw [nsa_aux_s5_w1_zero_fun]
  intro hcon
  have hempty : {ω : Fin 2 | nsa_aux_s5_w0 ω = 0} = ∅ := by
    ext ω
    constructor
    · intro hmem
      simp only [Set.mem_ofPred_eq] at hmem
      have hsq := nsa_aux_s5_w0_sq ω
      rw [hmem] at hsq
      norm_num at hsq
    · intro hmem
      simp at hmem
  have hmem : {ω : Fin 2 | nsa_aux_s5_w0 ω = 0} ∈ ae nsa_aux_s5_μ := hcon
  rw [hempty, mem_ae_iff] at hmem
  simp only [Set.compl_empty] at hmem
  rw [nsa_aux_s5_μ_univ] at hmem
  exact one_ne_zero hmem

/-- Lemma 1 without the divergence hypothesis (d) is false, even from `W 0 = 0`. -/
theorem lemma1_needs_divergence :
    ¬ ∀ (Ω : Type) (m0 : MeasurableSpace Ω) (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
        (ℱ : Filtration ℕ m0) (α w B W : ℕ → Ω → ℝ) (C : ℝ),
      StronglyAdapted ℱ α → StronglyAdapted ℱ B → (∀ t, StronglyMeasurable[ℱ (t + 1)] (w t)) →
      (∀ t, IsCenteredNoise (ℱ t) μ (w t) (B t)) → (∀ᵐ ω ∂μ, ∀ t, 0 ≤ B t ω) →
      (∀ᵐ ω ∂μ, ∀ t, α t ω ∈ Set.Icc (0 : ℝ) 1) →
      (∀ᵐ ω ∂μ, ∀ n, ∑ t ∈ Finset.range n, α t ω ^ 2 ≤ C) →
      (∀ᵐ ω ∂μ, BddAbove (Set.range fun t => B t ω)) →
      (∀ᵐ ω ∂μ, ∀ t, W (t + 1) ω = (1 - α t ω) * W t ω + α t ω * w t ω) →
      (∀ ω, W 0 ω = 0) →
      ∀ᵐ ω ∂μ, Tendsto (fun t => W t ω) atTop (𝓝 0) := by
  intro h
  have ha_adapt : StronglyAdapted nsa_aux_s5_ℱ nsa_aux_s5_a1 := fun t => stronglyMeasurable_const
  have hB_adapt : StronglyAdapted nsa_aux_s5_ℱ nsa_aux_s5_B := fun t => stronglyMeasurable_const
  have hw_meas : ∀ t, StronglyMeasurable[nsa_aux_s5_ℱ (t + 1)] (nsa_aux_s5_w1 t) :=
    fun t => nsa_aux_s5_w1_meas t
  have hw : ∀ t, IsCenteredNoise (nsa_aux_s5_ℱ t) nsa_aux_s5_μ (nsa_aux_s5_w1 t) (nsa_aux_s5_B t) :=
    fun t => nsa_aux_s5_w1_centered t
  have ha01 : ∀ᵐ ω ∂nsa_aux_s5_μ, ∀ t, nsa_aux_s5_a1 t ω ∈ Set.Icc (0 : ℝ) 1 := by
    refine Eventually.of_forall fun ω t => ?_
    rw [Set.mem_Icc]
    by_cases ht : t = 0
    · subst ht
      rw [nsa_aux_s5_a1_zero]
      norm_num
    · obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht
      rw [nsa_aux_s5_a1_succ]
      norm_num
  have ha_sq : ∀ᵐ ω ∂nsa_aux_s5_μ, ∀ n, ∑ t ∈ Finset.range n, nsa_aux_s5_a1 t ω ^ 2 ≤ (1 : ℝ) :=
    Eventually.of_forall fun ω n => nsa_aux_s5_a1_sq_le n ω
  have hW : ∀ᵐ ω ∂nsa_aux_s5_μ, ∀ t, nsa_aux_s5_W1 (t + 1) ω
      = (1 - nsa_aux_s5_a1 t ω) * nsa_aux_s5_W1 t ω + nsa_aux_s5_a1 t ω * nsa_aux_s5_w1 t ω := by
    refine Eventually.of_forall fun ω t => ?_
    cases t with
    | zero =>
      rw [nsa_aux_s5_W1_succ, nsa_aux_s5_a1_zero, nsa_aux_s5_W1_zero, nsa_aux_s5_w1_zero]
      ring
    | succ t =>
      rw [nsa_aux_s5_W1_succ, nsa_aux_s5_a1_succ, nsa_aux_s5_W1_succ, nsa_aux_s5_w1_succ]
      ring
  have hW0 : ∀ ω, nsa_aux_s5_W1 0 ω = 0 := fun ω => nsa_aux_s5_W1_zero ω
  have hconc := h (Fin 2) ⊤ nsa_aux_s5_μ nsa_aux_s5_ℱ
    nsa_aux_s5_a1 nsa_aux_s5_w1 nsa_aux_s5_B nsa_aux_s5_W1 (1 : ℝ)
    ha_adapt hB_adapt hw_meas hw nsa_aux_s5_B_nonneg ha01 ha_sq nsa_aux_s5_B_bdd hW hW0
  exact nsa_aux_s5_ae_false_of_pointwise hconc (fun ω => nsa_aux_s5_W1_not_tendsto ω)

/-- Lemma 1 without the centering condition (a) is false, even from `W 0 = 0`: the conditional
second moment bound (b) alone does not suffice. -/
theorem lemma1_needs_centering :
    ¬ ∀ (Ω : Type) (m0 : MeasurableSpace Ω) (μ : Measure[m0] Ω) [IsProbabilityMeasure μ]
        (ℱ : Filtration ℕ m0) (α w B W : ℕ → Ω → ℝ) (C : ℝ),
      StronglyAdapted ℱ α → StronglyAdapted ℱ B → (∀ t, StronglyMeasurable[ℱ (t + 1)] (w t)) →
      (∀ t, μ⁻[fun ω => ENNReal.ofReal (w t ω ^ 2) | ℱ t] ≤ᵐ[μ]
        fun ω => ENNReal.ofReal (B t ω)) →
      (∀ᵐ ω ∂μ, ∀ t, 0 ≤ B t ω) →
      (∀ᵐ ω ∂μ, ∀ t, α t ω ∈ Set.Icc (0 : ℝ) 1) →
      (∀ᵐ ω ∂μ, Tendsto (fun n => ∑ t ∈ Finset.range n, α t ω) atTop atTop) →
      (∀ᵐ ω ∂μ, ∀ n, ∑ t ∈ Finset.range n, α t ω ^ 2 ≤ C) →
      (∀ᵐ ω ∂μ, BddAbove (Set.range fun t => B t ω)) →
      (∀ᵐ ω ∂μ, ∀ t, W (t + 1) ω = (1 - α t ω) * W t ω + α t ω * w t ω) →
      (∀ ω, W 0 ω = 0) →
      ∀ᵐ ω ∂μ, Tendsto (fun t => W t ω) atTop (𝓝 0) := by
  intro h
  have ha_adapt : StronglyAdapted nsa_aux_s5_Fbot nsa_aux_s5_a2 := fun t => stronglyMeasurable_const
  have hB_adapt : StronglyAdapted nsa_aux_s5_Fbot nsa_aux_s5_B := fun t => stronglyMeasurable_const
  have hw_meas : ∀ t, StronglyMeasurable[nsa_aux_s5_Fbot (t + 1)] (nsa_aux_s5_w2 t) :=
    fun t => stronglyMeasurable_const
  have hvar :
      ∀ t, nsa_aux_s5_μ⁻[fun ω => ENNReal.ofReal (nsa_aux_s5_w2 t ω ^ 2) | nsa_aux_s5_Fbot t]
      ≤ᵐ[nsa_aux_s5_μ] fun ω => ENNReal.ofReal (nsa_aux_s5_B t ω) :=
    fun t => nsa_aux_s5_var_one t
  have ha01 : ∀ᵐ ω ∂nsa_aux_s5_μ, ∀ t, nsa_aux_s5_a2 t ω ∈ Set.Icc (0 : ℝ) 1 :=
    Eventually.of_forall fun ω t => nsa_aux_s5_a2_mem t ω
  have hdiv : ∀ᵐ ω ∂nsa_aux_s5_μ,
      Tendsto (fun n => ∑ t ∈ Finset.range n, nsa_aux_s5_a2 t ω) atTop atTop :=
    Eventually.of_forall fun ω => nsa_aux_s5_a2_div ω
  have hsq : ∀ᵐ ω ∂nsa_aux_s5_μ, ∀ n, ∑ t ∈ Finset.range n, nsa_aux_s5_a2 t ω ^ 2 ≤ (2 : ℝ) :=
    Eventually.of_forall fun ω n => nsa_aux_s5_a2_sq_le n ω
  have hW : ∀ᵐ ω ∂nsa_aux_s5_μ, ∀ t, nsa_aux_s5_W2 (t + 1) ω
      = (1 - nsa_aux_s5_a2 t ω) * nsa_aux_s5_W2 t ω + nsa_aux_s5_a2 t ω * nsa_aux_s5_w2 t ω := by
    refine Eventually.of_forall fun ω t => ?_
    cases t with
    | zero =>
      rw [nsa_aux_s5_W2_succ, nsa_aux_s5_a2_zero, nsa_aux_s5_W2_zero]
      show (1 : ℝ) = (1 - 1) * 0 + 1 * 1
      norm_num
    | succ t =>
      rw [nsa_aux_s5_W2_succ, nsa_aux_s5_W2_succ]
      show (1 : ℝ) = (1 - nsa_aux_s5_a2 (t + 1) ω) * 1 + nsa_aux_s5_a2 (t + 1) ω * 1
      ring
  have hW0 : ∀ ω, nsa_aux_s5_W2 0 ω = 0 := fun ω => nsa_aux_s5_W2_zero ω
  have hconc := h (Fin 2) ⊤ nsa_aux_s5_μ nsa_aux_s5_Fbot
    nsa_aux_s5_a2 nsa_aux_s5_w2 nsa_aux_s5_B nsa_aux_s5_W2 (2 : ℝ)
    ha_adapt hB_adapt hw_meas hvar nsa_aux_s5_B_nonneg ha01 hdiv hsq nsa_aux_s5_B_bdd hW hW0
  exact nsa_aux_s5_ae_false_of_pointwise hconc (fun ω => nsa_aux_s5_W2_not_tendsto ω)

/-- The hypotheses of `ae_tendsto_zero` hold together for noise that is not almost surely zero,
for example a fair coin with `ℱ 0` trivial and `ℱ t` everything for `t ≥ 1`, `w 0 = ±1`,
`w t = 0` for `t ≥ 1`, `α t = 1 / (t + 1)`, `B = 1`, and `C` the sum of the series
`∑ t, (1 / (t + 1)) ^ 2`. -/
theorem ae_tendsto_zero_hypotheses_satisfiable :
    ∃ (Ω : Type) (m0 : MeasurableSpace Ω) (μ : Measure[m0] Ω) (_ : IsProbabilityMeasure μ)
      (ℱ : Filtration ℕ m0) (α w B : ℕ → Ω → ℝ) (C : ℝ),
      StronglyAdapted ℱ α ∧ StronglyAdapted ℱ B ∧ (∀ t, StronglyMeasurable[ℱ (t + 1)] (w t)) ∧
      (∀ t, IsCenteredNoise (ℱ t) μ (w t) (B t)) ∧
      (∀ᵐ ω ∂μ, ∀ t, α t ω ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n => ∑ t ∈ Finset.range n, α t ω) atTop atTop) ∧
      (∀ᵐ ω ∂μ, ∀ n, ∑ t ∈ Finset.range n, α t ω ^ 2 ≤ C) ∧
      (∀ᵐ ω ∂μ, BddAbove (Set.range fun t => B t ω)) ∧
      ¬ ∀ t, w t =ᵐ[μ] 0 := by
  refine ⟨Fin 2, ⊤, nsa_aux_s5_μ, nsa_aux_s5_prob, nsa_aux_s5_ℱ, nsa_aux_s5_a2, nsa_aux_s5_w1,
    nsa_aux_s5_B, (2 : ℝ), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun t => stronglyMeasurable_const
  · exact fun t => stronglyMeasurable_const
  · exact fun t => nsa_aux_s5_w1_meas t
  · exact fun t => nsa_aux_s5_w1_centered t
  · exact Eventually.of_forall fun ω t => nsa_aux_s5_a2_mem t ω
  · exact Eventually.of_forall fun ω => nsa_aux_s5_a2_div ω
  · exact Eventually.of_forall fun ω n => nsa_aux_s5_a2_sq_le n ω
  · exact nsa_aux_s5_B_bdd
  · intro hall
    exact nsa_aux_s5_w1_not_ae_zero (hall 0)

/-- `ae_tendsto_zero` applied to the model of `ae_tendsto_zero_hypotheses_satisfiable`: the
recursion started from `0` tends to `0` almost surely. -/
private theorem restart_coin_tendsto_zero :
    ∀ᵐ ω ∂nsa_aux_s5_μ,
      Tendsto (fun t => restart nsa_aux_s5_a2 nsa_aux_s5_w1 0 t ω) atTop (𝓝 0) :=
  ae_tendsto_zero (ℱ := nsa_aux_s5_ℱ) (α := nsa_aux_s5_a2) (w := nsa_aux_s5_w1)
    (B := nsa_aux_s5_B) (W := restart nsa_aux_s5_a2 nsa_aux_s5_w1 0) (C := 2)
    (fun _ => stronglyMeasurable_const) (fun _ => stronglyMeasurable_const)
    nsa_aux_s5_w1_meas nsa_aux_s5_w1_centered
    (Eventually.of_forall fun ω t => nsa_aux_s5_a2_mem t ω)
    (Eventually.of_forall fun ω => nsa_aux_s5_a2_div ω)
    (Eventually.of_forall fun ω n => nsa_aux_s5_a2_sq_le n ω) nsa_aux_s5_B_bdd
    (Eventually.of_forall fun ω t => by simp only [restart, Nat.zero_add])

/-- The model's recursion is not identically `0`: at time `1` it is the coin flip `±1`. -/
example (ω : Fin 2) : restart nsa_aux_s5_a2 nsa_aux_s5_w1 0 1 ω = nsa_aux_s5_w0 ω := by
  simp only [restart, Nat.zero_add, nsa_aux_s5_a2_zero, nsa_aux_s5_w1_zero]
  ring

/-- The contract reads a negative envelope as `0`: with envelope `-1` it is the contract with
envelope `0`. Where the fields are conditional moments (an a.e.-measurable `w`, a sub-σ-algebra
`m` and a σ-finite `μ.trim`), that contract asks the conditional second moment to vanish. -/
theorem isCenteredNoise_neg_one_iff {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {m : MeasurableSpace Ω} {w : Ω → ℝ} :
    IsCenteredNoise m μ w (fun _ => -1) ↔ IsCenteredNoise m μ w (fun _ => 0) := by
  have h : ENNReal.ofReal (-1) = ENNReal.ofReal 0 := by simp
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by simpa only [h] using h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by simpa only [h] using h1, h2⟩

/-- Outside the setting the contract is meant for, `μ⁻[· | m]` is `0`, so every `w` satisfies
the contract: here `m` is not a sub-σ-algebra of `m0`. -/
example {Ω : Type*} {m0 m : MeasurableSpace Ω} (hm : ¬ m ≤ m0) (μ : Measure[m0] Ω)
    (w B : Ω → ℝ) : IsCenteredNoise m μ w B := by
  refine ⟨?_, by simp [condLExp_of_not_le hm]⟩
  rw [condLExp_of_not_le hm]
  filter_upwards with ω
  simp

/-- The same holds when `μ.trim` is not σ-finite. -/
example {Ω : Type*} {m0 m : MeasurableSpace Ω} (hm : m ≤ m0) (μ : Measure[m0] Ω)
    (hσ : ¬ SigmaFinite (μ.trim hm)) (w B : Ω → ℝ) : IsCenteredNoise m μ w B := by
  refine ⟨?_, by simp [condLExp_of_not_sigmaFinite hm hσ]⟩
  rw [condLExp_of_not_sigmaFinite hm hσ]
  filter_upwards with ω
  simp

/-- Under the trivial σ-algebra on `Bool` every simple function is constant, so a function that
vanishes at `false` has lower integral `0` for every measure, whatever its value at `true`. -/
private theorem lintegral_bot_bool_eq_zero (μ : Measure[⊥] Bool) {f : Bool → ℝ≥0∞}
    (hf : f false = 0) : ∫⁻ b, f b ∂μ = 0 := by
  rw [lintegral_def]
  refine le_antisymm (iSup₂_le fun g hg => ?_) zero_le
  have hconst : ∀ b, g b = g false := by
    intro b
    rcases MeasurableSpace.measurableSet_bot_iff.mp
        (@SimpleFunc.measurableSet_fiber Bool ℝ≥0∞ ⊥ g (g false)) with h | h
    · exact absurd (show false ∈ g ⁻¹' {g false} from rfl) (by rw [h]; exact Set.notMem_empty _)
    · exact (show b ∈ g ⁻¹' {g false} by rw [h]; trivial)
  have hg0 : g = 0 := @SimpleFunc.ext Bool ℝ≥0∞ ⊥ g 0 fun b => by
    rw [hconst b]
    exact le_antisymm ((hg false).trans hf.le) zero_le
  rw [hg0, SimpleFunc.zero_lintegral]

/-- The contract alone does not make `w` a random variable, even with `m = m0` and a probability
measure. On `Bool` with the trivial σ-algebra and the measure `dirac true`, the noise with
`w false = 0` and `w true = 1` satisfies the contract with envelope `0`, yet it is not almost
everywhere `0`: the lower integrals behind `μ⁻[· | m]` see only the measurable minorants of
`ofReal w` and `ofReal (w ^ 2)`, which are constant and vanish at `false`. The convergence
theorems exclude such noise by their measurability hypothesis on `w t`. -/
example : IsCenteredNoise ⊥ (@Measure.dirac Bool ⊥ true) (fun b => if b then 1 else 0)
      (fun _ => 0) ∧
    ¬ (fun b : Bool => if b then (1 : ℝ) else 0) =ᵐ[@Measure.dirac Bool ⊥ true] 0 := by
  refine ⟨⟨?_, ?_⟩, fun h => ?_⟩
  · rw [condLExp_bot, lintegral_bot_bool_eq_zero _ (by simp)]
    exact Eventually.of_forall fun _ => zero_le
  · rw [condLExp_bot, condLExp_bot, lintegral_bot_bool_eq_zero _ (by simp),
      lintegral_bot_bool_eq_zero _ (by simp)]
  · have h1 := @Measure.dirac_apply_of_mem Bool ⊥
      {a | ¬ (fun b : Bool => if b then (1 : ℝ) else 0) a = (0 : Bool → ℝ) a} true (by simp)
    exact one_ne_zero (h1.symm.trans (ae_iff.mp h))

section Interface

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- `IsCenteredNoise.of_memLp` and `IsCenteredNoise.div` compose: square-integrable noise with the
usual conditional moments, divided by an `m`-measurable `G ≥ G₀ > 0`, satisfies the contract
with envelope `B / G ^ 2`. -/
example [IsFiniteMeasure μ] {m : MeasurableSpace Ω} {w B G : Ω → ℝ} {G₀ : ℝ}
    (hwm : Measurable[m0] w) (hw2 : MemLp w 2 μ) (hmean : μ[w | m] =ᵐ[μ] 0)
    (hsq : μ[fun ω => w ω ^ 2 | m] ≤ᵐ[μ] B) (hGm : StronglyMeasurable[m] G) (hG₀ : 0 < G₀)
    (hG : ∀ᵐ ω ∂μ, G₀ ≤ G ω) :
    IsCenteredNoise m μ (fun ω => w ω / G ω) (fun ω => B ω / G ω ^ 2) :=
  (IsCenteredNoise.of_memLp hw2 hmean hsq).div hwm hGm hG₀ hG

/-- The localized moment bridge, on an `m`-measurable event on which `B ≤ k`, for a constant
`k ≥ 0`, gives the Bochner centering of the localized noise. -/
example [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m0) {w B : Ω → ℝ}
    (hwm : Measurable[m0] w) (hw : IsCenteredNoise m μ w B) {A : Set Ω}
    (hA : MeasurableSet[m] A) {k : ℝ} (hk : 0 ≤ k) (hBk : ∀ ω ∈ A, B ω ≤ k) :
    μ[A.indicator w | m] =ᵐ[μ] 0 :=
  (hw.localize hm hwm hA hk hBk).2.1

variable [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {α w B W : ℕ → Ω → ℝ} {C : ℝ}

/-- Lemma 1 takes its hypotheses in the order of the source's conditions. -/
example (hα_adapted : StronglyAdapted ℱ α) (hB_adapted : StronglyAdapted ℱ B)
    (hw_meas : ∀ t, StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw : ∀ t, IsCenteredNoise (ℱ t) μ (w t) (B t))
    (hα01 : ∀ᵐ ω ∂μ, ∀ t, α t ω ∈ Set.Icc (0 : ℝ) 1)
    (hα_div : ∀ᵐ ω ∂μ, Tendsto (fun n => ∑ t ∈ Finset.range n, α t ω) atTop atTop)
    (hα_sq : ∀ᵐ ω ∂μ, ∀ n, ∑ t ∈ Finset.range n, α t ω ^ 2 ≤ C)
    (hB_bdd : ∀ᵐ ω ∂μ, BddAbove (Set.range fun t => B t ω))
    (hW : ∀ᵐ ω ∂μ, ∀ t, W (t + 1) ω = (1 - α t ω) * W t ω + α t ω * w t ω) :
    ∀ᵐ ω ∂μ, Tendsto (fun t => W t ω) atTop (𝓝 0) :=
  ae_tendsto_zero hα_adapted hB_adapted hw_meas hw hα01 hα_div hα_sq hB_bdd hW

/-- Lemma 2 at a fixed tolerance `δ > 0`. -/
example (hα_adapted : StronglyAdapted ℱ α) (hB_adapted : StronglyAdapted ℱ B)
    (hw_meas : ∀ t, StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw : ∀ t, IsCenteredNoise (ℱ t) μ (w t) (B t))
    (hα01 : ∀ᵐ ω ∂μ, ∀ t, α t ω ∈ Set.Icc (0 : ℝ) 1)
    (hα_div : ∀ᵐ ω ∂μ, Tendsto (fun n => ∑ t ∈ Finset.range n, α t ω) atTop atTop)
    (hα_sq : ∀ᵐ ω ∂μ, ∀ n, ∑ t ∈ Finset.range n, α t ω ^ 2 ≤ C)
    (hB_bdd : ∀ᵐ ω ∂μ, BddAbove (Set.range fun t => B t ω)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂μ, ∃ T, ∀ t₀ ≥ T, ∀ n, |restart α w t₀ n ω| ≤ δ := by
  filter_upwards [ae_uniform_tail_restart hα_adapted hB_adapted hw_meas hw hα01
    hα_div hα_sq hB_bdd] with ω hω using hω δ hδ

/-- The finite-coordinate form at a fixed tolerance `δ > 0`: every coordinate tends to `0`, and
one restart threshold serves all coordinates. -/
example {ι : Type*} [Finite ι] {α w B W : ι → ℕ → Ω → ℝ}
    (hα_adapted : ∀ i, StronglyAdapted ℱ (α i)) (hB_adapted : ∀ i, StronglyAdapted ℱ (B i))
    (hw_meas : ∀ i t, StronglyMeasurable[ℱ (t + 1)] (w i t))
    (hw : ∀ i t, IsCenteredNoise (ℱ t) μ (w i t) (B i t))
    (hα01 : ∀ᵐ ω ∂μ, ∀ i t, α i t ω ∈ Set.Icc (0 : ℝ) 1)
    (hα_div : ∀ᵐ ω ∂μ, ∀ i, Tendsto (fun n => ∑ t ∈ Finset.range n, α i t ω) atTop atTop)
    (hα_sq : ∀ᵐ ω ∂μ, ∀ i n, ∑ t ∈ Finset.range n, α i t ω ^ 2 ≤ C)
    (hB_bdd : ∀ᵐ ω ∂μ, ∀ i, BddAbove (Set.range fun t => B i t ω))
    (hW : ∀ᵐ ω ∂μ, ∀ i t, W i (t + 1) ω = (1 - α i t ω) * W i t ω + α i t ω * w i t ω)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂μ, (∀ i, Tendsto (fun t => W i t ω) atTop (𝓝 0)) ∧
      ∃ T, ∀ i, ∀ t₀ ≥ T, ∀ n, |restart (α i) (w i) t₀ n ω| ≤ δ := by
  filter_upwards [ae_tendsto_zero_and_uniform_tail_fintype hα_adapted hB_adapted hw_meas hw
    hα01 hα_div hα_sq hB_bdd hW] with ω hω using ⟨hω.1, hω.2 δ hδ⟩

end Interface

end Cslib.MachineLearning.NoiseAveragingTests

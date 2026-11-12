/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Finite-class holdout bound

For finitely many candidate losses `f j : Z → ℝ`, `j : Fin M`, fixed before sampling, measurable
and almost surely in `[0, 1]`, and an iid validation sample `S : Fin n → Z` from `μ`, every
empirical mean `n⁻¹ ∑ i, f j (S i)` is within `ε` of `∫ z, f j z ∂μ` except on a set of
probability at most `2 M exp (-2 n ε ^ 2)`.

The proof applies Hoeffding's lemma and Mathlib's sub-Gaussian tail bound to each candidate
(two-sided), then a finite union bound. No risk or sample-law definitions are introduced: the
empirical and population means are written out, and the sample law is `Measure.pi`.

## Main results

* `ProbabilityTheory.measure_exists_abs_empirical_sub_integral_ge_le`: the finite-class bound.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

private lemma measureReal_abs_empirical_sub_integral_ge_le_single
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) (g : Z → ℝ) (hg : Measurable g)
    (hbd : ∀ᵐ z ∂μ, g z ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin n => μ).real
        {S : Fin n → Z | ε ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n, g (S i) - ∫ z, g z ∂μ|} ≤
      2 * Real.exp (-2 * (n : ℝ) * ε ^ 2) := by
  set P := Measure.pi fun _ : Fin n => μ
  set m := ∫ z, g z ∂μ with hm
  set Y : Fin n → (Fin n → Z) → ℝ := fun i S => g (S i) - m with hY
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmp : ∀ i : Fin n, MeasurePreserving (Function.eval i) P μ :=
    fun i => measurePreserving_eval (fun _ : Fin n => μ) i
  have hint : ∀ i : Fin n, ∫ S, g (S i) ∂P = m := by
    intro i
    rw [hm, ← (hmp i).map_eq,
      integral_map (measurable_pi_apply i).aemeasurable hg.aestronglyMeasurable]
  have hc : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal) = 1 / 4 := by
    have h1 : ‖(1 : ℝ) - 0‖₊ = 1 := by simp
    rw [h1]
    norm_num
  have hsub : ∀ i, HasSubgaussianMGF (Y i) (1 / 4 : NNReal) P := by
    intro i
    have h := hasSubgaussianMGF_of_mem_Icc (μ := P) (X := fun S => g (S i))
      (hg.comp (measurable_pi_apply i)).aemeasurable
      ((hmp i).quasiMeasurePreserving.ae hbd)
    rw [hint i, hc] at h
    exact h
  have hXindep : iIndepFun (fun i (S : Fin n → Z) => g (S i)) P :=
    iIndepFun_pi (X := fun _ => g) (fun _ => hg.aemeasurable)
  have hYindep : iIndepFun Y P :=
    hXindep.comp (fun _ x => x - m) (fun _ => measurable_id.sub_const m)
  have hεn : (0 : ℝ) ≤ n * ε := mul_nonneg hnR.le hε
  have hcsum : ↑(∑ _i ∈ (Finset.univ : Finset (Fin n)), (1 / 4 : NNReal))
      = (n : ℝ) / 4 := by
    push_cast
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hexp_eq : -((n : ℝ) * ε) ^ 2
        / (2 * ↑(∑ _i ∈ (Finset.univ : Finset (Fin n)), (1 / 4 : NNReal)))
      = -2 * (n : ℝ) * ε ^ 2 := by
    rw [hcsum]
    field_simp
    ring
  have hup : P.real {S | (n : ℝ) * ε ≤ ∑ i ∈ Finset.univ, Y i S} ≤
      Real.exp (-2 * (n : ℝ) * ε ^ 2) := by
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (X := Y)
      (c := fun _ => (1 / 4 : NNReal)) (s := Finset.univ) hYindep
      (fun i _ => hsub i) hεn
    rwa [hexp_eq] at h
  have hZindep : iIndepFun (fun i => -Y i) P :=
    hYindep.comp (fun _ => Neg.neg) (fun _ => measurable_neg)
  have hlow : P.real {S | (n : ℝ) * ε ≤ ∑ i ∈ Finset.univ, (-Y i) S} ≤
      Real.exp (-2 * (n : ℝ) * ε ^ 2) := by
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (X := fun i => -Y i) (c := fun _ => (1 / 4 : NNReal)) (s := Finset.univ)
      hZindep (fun i _ => (hsub i).neg) hεn
    rwa [hexp_eq] at h
  have hsum : ∀ S : Fin n → Z, ∑ i ∈ Finset.univ, Y i S
      = (n : ℝ) * ((n : ℝ)⁻¹ * ∑ i : Fin n, g (S i) - m) := by
    intro S
    simp only [hY, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hset : {S : Fin n → Z | ε ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n, g (S i) - m|} ⊆
      {S | (n : ℝ) * ε ≤ ∑ i ∈ Finset.univ, Y i S} ∪
        {S | (n : ℝ) * ε ≤ ∑ i ∈ Finset.univ, (-Y i) S} := by
    intro S hS
    have hS' : ε ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n, g (S i) - m| := hS
    have hneg : ∑ i ∈ Finset.univ, (-Y i) S = -∑ i ∈ Finset.univ, Y i S := by
      simp only [Pi.neg_apply, Finset.sum_neg_distrib]
    rcases le_abs'.mp hS' with h | h
    · right
      change (n : ℝ) * ε ≤ ∑ i ∈ Finset.univ, (-Y i) S
      rw [hneg, hsum S]
      nlinarith
    · left
      change (n : ℝ) * ε ≤ ∑ i ∈ Finset.univ, Y i S
      rw [hsum S]
      nlinarith
  calc P.real {S : Fin n → Z | ε ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n, g (S i) - m|}
        ≤ P.real ({S | (n : ℝ) * ε ≤ ∑ i ∈ Finset.univ, Y i S} ∪
            {S | (n : ℝ) * ε ≤ ∑ i ∈ Finset.univ, (-Y i) S}) :=
          measureReal_mono hset (measure_ne_top P _)
      _ ≤ P.real {S | (n : ℝ) * ε ≤ ∑ i ∈ Finset.univ, Y i S} +
            P.real {S | (n : ℝ) * ε ≤ ∑ i ∈ Finset.univ, (-Y i) S} :=
          measureReal_union_le _ _
      _ ≤ Real.exp (-2 * (n : ℝ) * ε ^ 2) + Real.exp (-2 * (n : ℝ) * ε ^ 2) :=
          add_le_add hup hlow
      _ = 2 * Real.exp (-2 * (n : ℝ) * ε ^ 2) := by ring

/-- **Finite-class holdout bound.** For `M` fixed measurable losses with values in `[0, 1]` and
`n > 0` iid draws from `μ`, some empirical mean deviates from its population mean by at least
`ε` with probability at most `2 M exp (-2 n ε ^ 2)`. -/
theorem measure_exists_abs_empirical_sub_integral_ge_le
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    {M n : ℕ} (hn : 0 < n) (f : Fin M → Z → ℝ) (hf : ∀ j, Measurable (f j))
    (hbd : ∀ j, ∀ᵐ z ∂μ, f j z ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin n => μ).real
        {S : Fin n → Z | ∃ j : Fin M,
          ε ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S i) - ∫ z, f j z ∂μ|} ≤
      2 * (M : ℝ) * Real.exp (-2 * (n : ℝ) * ε ^ 2) := by
  have hU : {S : Fin n → Z | ∃ j : Fin M,
      ε ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S i) - ∫ z, f j z ∂μ|} =
      ⋃ j : Fin M, {S : Fin n → Z |
        ε ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S i) - ∫ z, f j z ∂μ|} := by
    ext S
    simp
  rw [hU]
  calc _ ≤ ∑ j : Fin M, (Measure.pi fun _ : Fin n => μ).real {S : Fin n → Z |
          ε ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S i) - ∫ z, f j z ∂μ|} :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin M, 2 * Real.exp (-2 * (n : ℝ) * ε ^ 2) :=
        Finset.sum_le_sum fun j _ =>
          measureReal_abs_empirical_sub_integral_ge_le_single μ hn (f j) (hf j) (hbd j) hε
    _ = 2 * (M : ℝ) * Real.exp (-2 * (n : ℝ) * ε ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end ProbabilityTheory

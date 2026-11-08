/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.SimpleFunc
public import Mathlib.Topology.Order.Basic

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MathlibExt.MeasureTheory.Function.SimpleFuncUniformApprox

/-!
# Approximation of nonnegative measurable functions by simple functions

For a nonnegative measurable function `f : α → ℝ≥0∞` there is a sequence of
simple functions `φₙ` with `0 ≤ φ₀ ≤ φ₁ ≤ ⋯ ≤ f` converging pointwise to `f`,
and the convergence is uniform on every set where `f` is bounded. The
monotone pointwise part is Mathlib's `SimpleFunc.eapprox` machinery
(`SimpleFunc.monotone_eapprox`, `SimpleFunc.tendsto_eapprox`); the uniform
part on `{f ≤ B}` is the new content here — Mathlib has no uniform version
of `tendsto_eapprox` — and is proved by approximating `f a` from below by a
rational multiple `j * q` of a fixed rational step `q < ε`, using that only
finitely many such multiples lie in `[0, B]`.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/MeasureTheory.lean`,
`MeasureTheory.SimpleFunc.exists_monotone_tendsto` (Theorem, March 23, 2021).
-/

/-- **Uniform approximation by `eapprox` on sets where `f` is bounded.**
For a measurable `f : α → ℝ≥0∞`, a bound `B ≠ ⊤` and `ε ≠ 0`, there is an
`N` such that for all `n ≥ N` and all `a` with `f a ≤ B`, the simple-function
approximation `eapprox f n` is within `ε` of `f a` from below. -/
theorem eapprox_sub_lt_of_le
    {α : Type*} [MeasurableSpace α] {f : α → ℝ≥0∞} (hf : Measurable f)
    {B ε : ℝ≥0∞} (hB : B ≠ ⊤) (hε : ε ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a, f a ≤ B → f a - SimpleFunc.eapprox f n a < ε := by
  by_cases hε_top : ε = ⊤
  · exact ⟨0, fun n _ a ha => by
      rw [hε_top]
      exact tsub_le_self.trans_lt (lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top hB ha))⟩
  have hε_pos : (0 : ℝ≥0∞) < ε := pos_iff_ne_zero.mpr hε
  have hB_lt : B < ⊤ := lt_top_iff_ne_top.mpr hB
  obtain ⟨r, hr_pos, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε_pos
  have hr_real_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast ENNReal.coe_pos.mp hr_pos
  obtain ⟨q, hq_pos_real, hqr⟩ := exists_rat_btwn hr_real_pos
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hq_lt_ε : ENNReal.ofReal (q : ℝ) < ε := by
    calc ENNReal.ofReal (q : ℝ) < (r : ℝ≥0∞) := by
            rw [← ENNReal.ofReal_coe_nnreal]
            exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt hq_pos)).mpr hqr
      _ < ε := hrε
  set k := Nat.ceil (B.toReal / (q : ℝ))
  set N := 1 + (Finset.range (k + 1)).sup (fun i => Encodable.encode ((↑i : ℚ) * q))
  use N
  intro n hn a ha
  by_cases hfa_zero : f a = 0
  · simp [hfa_zero, hε_pos]
  have hfa_lt : f a < ⊤ := lt_of_le_of_lt ha hB_lt
  have hfa_ne_top : f a ≠ ⊤ := hfa_lt.ne
  set j := Nat.floor ((f a).toReal / (q : ℝ))
  have h_div_nn : (0 : ℝ) ≤ (f a).toReal / (q : ℝ) :=
    div_nonneg ENNReal.toReal_nonneg (le_of_lt hq_pos)
  have h_j_le : (↑j : ℝ) * (q : ℝ) ≤ (f a).toReal := by
    nlinarith [Nat.floor_le h_div_nn, div_mul_cancel₀ (f a).toReal (ne_of_gt hq_pos)]
  have h_diff_lt : (f a).toReal - ↑j * (q : ℝ) < (q : ℝ) := by
    nlinarith [Nat.lt_floor_add_one ((f a).toReal / (q : ℝ)),
               div_mul_cancel₀ (f a).toReal (ne_of_gt hq_pos)]
  have hj_le_k : j ≤ k :=
    (Nat.floor_le_ceil _).trans (Nat.ceil_le_ceil
      (div_le_div_of_nonneg_right ((ENNReal.toReal_le_toReal hfa_ne_top hB).mpr ha)
        (le_of_lt hq_pos)))
  have h_encode_lt : Encodable.encode ((↑j : ℚ) * q) < N := by
    have hmem : j ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
    have h : Encodable.encode ((↑j : ℚ) * q) ≤
        (Finset.range (k + 1)).sup (fun i => Encodable.encode ((↑i : ℚ) * q)) :=
      Finset.le_sup_of_le hmem le_rfl
    omega
  have h_embed_val : SimpleFunc.ennrealRatEmbed (Encodable.encode ((↑j : ℚ) * q)) =
      ENNReal.ofReal (↑j * (q : ℝ)) := by
    rw [SimpleFunc.ennrealRatEmbed_encode]; simp [ENNReal.ofReal, Rat.cast_mul, Rat.cast_natCast]
  have h_embed_le : SimpleFunc.ennrealRatEmbed (Encodable.encode ((↑j : ℚ) * q)) ≤ f a := by
    rw [h_embed_val, ENNReal.ofReal_le_iff_le_toReal hfa_ne_top]; exact_mod_cast h_j_le
  have h_eapprox_ge : ENNReal.ofReal (↑j * (q : ℝ)) ≤ SimpleFunc.eapprox f n a := by
    rw [← h_embed_val]
    have h_step : SimpleFunc.ennrealRatEmbed (Encodable.encode ((↑j : ℚ) * q)) ≤
        SimpleFunc.eapprox f (Encodable.encode ((↑j : ℚ) * q) + 1) a := by
      have h := SimpleFunc.approx_apply a hf (i := SimpleFunc.ennrealRatEmbed)
        (n := Encodable.encode ((↑j : ℚ) * q) + 1)
      change SimpleFunc.ennrealRatEmbed _ ≤
        (SimpleFunc.approx SimpleFunc.ennrealRatEmbed f _) a; rw [h]
      refine le_trans ?_ (Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self _)))
      simp [h_embed_le]
    exact h_step.trans (SimpleFunc.monotone_eapprox f (by omega) a)
  calc f a - SimpleFunc.eapprox f n a
      ≤ f a - ENNReal.ofReal (↑j * (q : ℝ)) := tsub_le_tsub_left h_eapprox_ge _
    _ < ENNReal.ofReal (q : ℝ) := by
        rw [← ENNReal.ofReal_toReal hfa_ne_top]
        rw [← ENNReal.ofReal_sub _ (show (0 : ℝ) ≤ ↑j * (q : ℝ) from by positivity)]
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)).mpr h_diff_lt
    _ < ε := hq_lt_ε

/-- **Approximation of nonnegative measurable functions by simple functions.**
For any nonnegative measurable `f : α → ℝ≥0∞`, there is a sequence of simple
functions `φₙ` such that: (a) `0 ≤ φ₀ ≤ φ₁ ≤ ⋯ ≤ f` pointwise; (b) `φₙ → f`
pointwise; and (c) for every bound `B < ∞` and every `ε > 0`, `f - φₙ < ε`
uniformly on `{a | f a ≤ B}` for all large `n`. -/
theorem exists_monotone_tendsto
    {α : Type*} [MeasurableSpace α] {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∃ φ : ℕ → SimpleFunc α ℝ≥0∞,
      ((∀ n a, φ n a ≤ f a) ∧ (Monotone fun n => (φ n : α → ℝ≥0∞))) ∧
      (∀ a, Tendsto (fun n => φ n a) atTop (𝓝 (f a))) ∧
      (∀ B : ℝ≥0∞, B ≠ ⊤ → ∀ ε : ℝ≥0∞, ε ≠ 0 →
        ∃ N : ℕ, ∀ n ≥ N, ∀ a, f a ≤ B → f a - φ n a < ε) := by
  refine ⟨SimpleFunc.eapprox f, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact fun n a =>
      (SimpleFunc.iSup_eapprox_apply hf a ▸
        le_iSup (fun n => (SimpleFunc.eapprox f n) a) n)
  · exact fun _ _ h a => SimpleFunc.monotone_eapprox f h a
  · exact fun a => SimpleFunc.tendsto_eapprox hf a
  · exact fun B hB ε hε => eapprox_sub_lt_of_le hf hB hε

end MathlibExt.MeasureTheory.Function.SimpleFuncUniformApprox

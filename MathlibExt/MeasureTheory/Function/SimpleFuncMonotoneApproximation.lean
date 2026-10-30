/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.SimpleFunc

@[expose] public section

/-!
# Monotone approximation by simple functions, uniform on bounded sets

For a nonnegative measurable function `f : α → ℝ≥0∞` there is a sequence of
simple functions `φ n` increasing pointwise to `f`, and the convergence is
uniform on every set where `f` is bounded: for `B ≠ ⊤` and `ε ≠ 0` there is
`N` such that `f a - φ n a < ε` for all `n ≥ N` and all `a` with `f a ≤ B`.

Mathlib already has the pointwise ingredients for this statement, as lemmas
about `SimpleFunc.eapprox`: monotonicity (`SimpleFunc.monotone_eapprox`),
pointwise convergence (`SimpleFunc.tendsto_eapprox`), and the fact that the
approximants stay below `f` (`SimpleFunc.iSup_eapprox_apply`). What Mathlib
does not have is the bundled statement, and in particular not the uniform
convergence on bounded sets (part (c) below). The proof of (c) is the one from
the source: pick a rational mesh `q` smaller than `ε`, approximate `f a` from
below by a mesh multiple `j * q`, and take `N` larger than the finitely many
`Encodable.encode` indices of the mesh multiples up to `B`.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/MeasureTheory.lean`,
`MeasureTheory.SimpleFunc.exists_monotone_tendsto`
(Theorem, March 23, 2021). Two API updates relative to the v1 proof:
`SimpleFunc.ennrealRatEmbed_encode` now gives `Real.toNNReal q` (used via
`ENNReal.ofNNReal_toNNReal`), and the final real-to-`ℝ≥0∞` subtraction step
uses `ENNReal.ofReal_sub` from `Mathlib/Basic/ENNReal/Operations.lean`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MathlibExt.MeasureTheory.Function.SimpleFuncMonotoneApproximation

/-- Monotone approximation of a nonnegative measurable function by simple
functions, with uniform convergence on every set where the function is
bounded. -/
theorem exists_monotone_tendsto {α : Type*} [MeasurableSpace α] {f : α → ℝ≥0∞}
    (hf : Measurable f) :
    ∃ φ : ℕ → SimpleFunc α ℝ≥0∞,
      ((∀ n a, φ n a ≤ f a) ∧ (Monotone fun n => (φ n : α → ℝ≥0∞))) ∧
      (∀ a, Tendsto (fun n => φ n a) atTop (𝓝 (f a))) ∧
      (∀ B : ℝ≥0∞, B ≠ ⊤ → ∀ ε : ℝ≥0∞, ε ≠ 0 →
        ∃ N : ℕ, ∀ n ≥ N, ∀ a, f a ≤ B → f a - φ n a < ε) := by
  refine ⟨SimpleFunc.eapprox f, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro n a
    calc (SimpleFunc.eapprox f n) a
        ≤ ⨆ m, (SimpleFunc.eapprox f m) a := le_iSup (fun m => (SimpleFunc.eapprox f m) a) n
      _ = f a := SimpleFunc.iSup_eapprox_apply hf a
  · exact fun _ _ h a => SimpleFunc.monotone_eapprox f h a
  · exact fun a => SimpleFunc.tendsto_eapprox hf a
  · intro B hB ε hε
    by_cases hε_top : ε = ⊤
    · exact ⟨0, fun n _ a ha => by
        rw [hε_top]
        exact tsub_le_self.trans_lt
          (lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top hB ha))⟩
    have hε_pos : (0 : ℝ≥0∞) < ε := pos_iff_ne_zero.mpr hε
    have hB_lt : B < ⊤ := lt_top_iff_ne_top.mpr hB
    obtain ⟨r, hr_pos, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε_pos
    have hr_real_pos : (0 : ℝ) < (r : ℝ) := by
      exact_mod_cast ENNReal.coe_pos.mp hr_pos
    obtain ⟨q, hq_pos_real, hqr⟩ := exists_rat_btwn hr_real_pos
    have hq_pos : (0 : ℝ) < (q : ℝ) := hq_pos_real
    have hq_lt_ε : ENNReal.ofReal (q : ℝ) < ε := by
      calc ENNReal.ofReal (q : ℝ) < (r : ℝ≥0∞) := by
              rw [← ENNReal.ofReal_coe_nnreal]
              exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt hq_pos)).mpr hqr
        _ < ε := hrε
    use 1 + (Finset.range (Nat.ceil (B.toReal / (q : ℝ)) + 1)).sup
      (fun i => Encodable.encode ((↑i : ℚ) * q))
    intro n hn a ha
    by_cases hfa_zero : f a = 0
    · rw [hfa_zero, zero_tsub]
      exact hε_pos
    have hfa_lt : f a < ⊤ := lt_of_le_of_lt ha hB_lt
    have hfa_ne_top : f a ≠ ⊤ := hfa_lt.ne
    -- Abbreviate the mesh index: this hides `(f a).toReal` inside `j`, so the
    -- `← ENNReal.ofReal_toReal` rewrite in the final calculation only touches
    -- the standalone `f a`.
    set j : ℕ := Nat.floor ((f a).toReal / (q : ℝ)) with hj_def
    have h_div_nn : (0 : ℝ) ≤ (f a).toReal / (q : ℝ) :=
      div_nonneg ENNReal.toReal_nonneg (le_of_lt hq_pos)
    have hfl : (↑j : ℝ) ≤ (f a).toReal / (q : ℝ) := by
      rw [hj_def]
      exact Nat.floor_le h_div_nn
    have h_j_le : (↑j : ℝ) * (q : ℝ) ≤ (f a).toReal := by
      nlinarith [hfl, div_mul_cancel₀ (f a).toReal (ne_of_gt hq_pos)]
    have hlt : (f a).toReal / (q : ℝ) < ↑j + 1 := by
      rw [hj_def]
      exact Nat.lt_floor_add_one _
    have h_diff_lt : (f a).toReal - ↑j * (q : ℝ) < (q : ℝ) := by
      nlinarith [hlt, div_mul_cancel₀ (f a).toReal (ne_of_gt hq_pos)]
    have hj_le_k : j ≤ Nat.ceil (B.toReal / (q : ℝ)) := by
      rw [hj_def]
      exact (Nat.floor_le_ceil _).trans (Nat.ceil_le_ceil
        (div_le_div_of_nonneg_right ((ENNReal.toReal_le_toReal hfa_ne_top hB).mpr ha)
          (le_of_lt hq_pos)))
    have h_encode_lt : Encodable.encode ((↑j : ℚ) * q) <
          1 + (Finset.range (Nat.ceil (B.toReal / (q : ℝ)) + 1)).sup
            (fun i => Encodable.encode ((↑i : ℚ) * q)) := by
      have hmem : j ∈ Finset.range (Nat.ceil (B.toReal / (q : ℝ)) + 1) :=
        Finset.mem_range.mpr (by omega)
      have h : Encodable.encode ((↑j : ℚ) * q) ≤
          (Finset.range (Nat.ceil (B.toReal / (q : ℝ)) + 1)).sup
            (fun i => Encodable.encode ((↑i : ℚ) * q)) :=
        Finset.le_sup_of_le hmem le_rfl
      omega
    have h_embed_val : SimpleFunc.ennrealRatEmbed (Encodable.encode ((↑j : ℚ) * q)) =
        ENNReal.ofReal (↑j * (q : ℝ)) := by
      rw [SimpleFunc.ennrealRatEmbed_encode, ENNReal.ofNNReal_toNNReal, Rat.cast_mul,
        Rat.cast_natCast]
    have h_embed_le : SimpleFunc.ennrealRatEmbed (Encodable.encode ((↑j : ℚ) * q)) ≤ f a := by
      rw [h_embed_val, ENNReal.ofReal_le_iff_le_toReal hfa_ne_top]
      exact_mod_cast h_j_le
    have h_eapprox_ge : ENNReal.ofReal (↑j * (q : ℝ)) ≤
        SimpleFunc.eapprox f n a := by
      rw [← h_embed_val]
      have h_step : SimpleFunc.ennrealRatEmbed (Encodable.encode ((↑j : ℚ) * q)) ≤
          SimpleFunc.eapprox f (Encodable.encode ((↑j : ℚ) * q) + 1) a := by
        have h := SimpleFunc.approx_apply a hf
          (i := SimpleFunc.ennrealRatEmbed)
          (n := Encodable.encode ((↑j : ℚ) * q) + 1)
        change SimpleFunc.ennrealRatEmbed _ ≤
          (SimpleFunc.approx SimpleFunc.ennrealRatEmbed f _) a
        rw [h]
        refine le_trans ?_ (Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self _)))
        simp [h_embed_le]
      exact h_step.trans (SimpleFunc.monotone_eapprox f (by omega) a)
    calc f a - SimpleFunc.eapprox f n a
        ≤ f a - ENNReal.ofReal (↑j * (q : ℝ)) :=
          tsub_le_tsub_left h_eapprox_ge _
      _ < ENNReal.ofReal (q : ℝ) := by
          rw [← ENNReal.ofReal_toReal hfa_ne_top]
          rw [← ENNReal.ofReal_sub _ (show (0 : ℝ) ≤ ↑j * (q : ℝ) from by positivity)]
          exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)).mpr h_diff_lt
      _ < ε := hq_lt_ε

end MathlibExt.MeasureTheory.Function.SimpleFuncMonotoneApproximation

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
public import Mathlib.Combinatorics.SimpleGraph.Extremal.TuranDensity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Turán density of complete graphs

Mathlib proves Turán's theorem (`SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph`),
identifies the extremal number of `K_{r+1}` with the number of edges of the Turán graph
`T(n, r)` (`SimpleGraph.extremalNumber_top`), bounds it above by `(1 - 1/r) n ^ 2 / 2`
(`SimpleGraph.mul_turanNumber_le`) and defines the Turán density (`SimpleGraph.turanDensity`).
This file computes the density: `π(K_{r+1}) = 1 - 1/r` for `r ≥ 1`
(`turanDensity_completeGraph`). The lower bound `2 r t(n, r) ≥ (r - 1)(n ^ 2 - r ^ 2)` on the
Turán number (`turanNumber_lower_bound`) follows from Mathlib's recursion
`t(n + r, r) = t(n, r) + n (r - 1) + C(r, 2)` (`SimpleGraph.turanNumber_add`).

`π(K₃) = 1/2` is the density form of Mantel's theorem.

## References

* P. Turán, *On an extremal problem in graph theory* (in Hungarian), Mat. Fiz. Lapok 48 (1941),
  436-452.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.TuranDensityComplete

open Filter Topology _root_.SimpleGraph

/-- **Lower bound on the Turán number.** For `r ≥ 1` and every `n`, the Turán graph `T(n, r)`
has at least `(1 - 1/r)(n ^ 2 - r ^ 2) / 2` edges: `(r - 1)(n ^ 2 - r ^ 2) ≤ 2 r t(n, r)`. -/
theorem turanNumber_lower_bound {r : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    ((r : ℝ) - 1) * ((n : ℝ) ^ 2 - (r : ℝ) ^ 2) ≤ 2 * r * (turanNumber n r : ℝ) := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < r
    · have hnr : (n : ℝ) < r := by exact_mod_cast hn
      have h1 : (n : ℝ) ^ 2 - (r : ℝ) ^ 2 ≤ 0 := by nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      have h2 : (0 : ℝ) ≤ 2 * r * (turanNumber n r : ℝ) := by positivity
      nlinarith
    · push Not at hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + r := ⟨n - r, by omega⟩
      have ihm := ih m (by omega)
      rw [turanNumber_add]
      have hc : ((r.choose 2 : ℕ) : ℝ) * 2 = r * (r - 1) := by
        rw [Nat.cast_choose_two]; ring
      push_cast [Nat.cast_sub hr]
      nlinarith [ihm, hc]

/-- **Upper bound on the Turán number (Mathlib), in real numbers.** For `r ≥ 1`,
`2 r t(n, r) ≤ (r - 1) n ^ 2`. -/
private theorem turanNumber_upper_bound {r : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    2 * r * (turanNumber n r : ℝ) ≤ ((r : ℝ) - 1) * (n : ℝ) ^ 2 := by
  have h := mul_turanNumber_le (n := n) (r := r)
  have h' : ((2 * r * turanNumber n r : ℕ) : ℝ) ≤ (((r - 1) * n ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast [Nat.cast_sub hr] at h'
  linarith

/-- **Turán density of complete graphs.** For `r ≥ 1`, the Turán density of the complete graph
on `r + 1` vertices is `1 - 1/r`: graphs on `n` vertices without `K_{r+1}` have at most
`(1 - 1/r + o(1)) C(n, 2)` edges, and the Turán graphs attain it (P. Turán, Mat. Fiz. Lapok 48
(1941), 436-452, with Mathlib's `SimpleGraph.extremalNumber_top` and
`SimpleGraph.mul_turanNumber_le`). For `r = 2` this is Mantel's density `π(K₃) = 1/2`. -/
theorem turanDensity_completeGraph {r : ℕ} (hr : 1 ≤ r) :
    turanDensity (⊤ : _root_.SimpleGraph (Fin (r + 1))) = 1 - 1 / r := by
  have : Nontrivial (Fin (r + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  set L : ℝ := 1 - 1 / r
  set f : ℕ → ℝ := fun n => (extremalNumber n (⊤ : _root_.SimpleGraph (Fin (r + 1))) : ℝ) /
    (n.choose 2 : ℝ) with hf
  -- `f n` is the Turán number over `C(n, 2)`.
  have hfeq : ∀ n, f n = (turanNumber n r : ℝ) / (n.choose 2 : ℝ) := fun n => by
    simp only [hf]
    rw [extremalNumber_top, Fintype.card_fin, Nat.add_sub_cancel]
  -- Upper and lower comparison functions.
  set u : ℕ → ℝ := fun n => L * ((n : ℝ) / ((n : ℝ) + (-1))) with hu
  set K : ℝ := ((r : ℝ) - 1) * r
  have hup : ∀ᶠ n in atTop, f n ≤ u n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    rw [hfeq, Nat.cast_choose_two, hu]
    have hpos : (0 : ℝ) < n * (n - 1) := by nlinarith
    have hn1 : (n : ℝ) + -1 ≠ 0 := by linarith
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hT := turanNumber_upper_bound hr n
    rw [div_le_iff₀ (by positivity)]
    have : L * ((n : ℝ) / ((n : ℝ) + -1)) * ((n : ℝ) * (n - 1) / 2) =
        ((r : ℝ) - 1) * n ^ 2 / (2 * r) := by
      simp only [L]; field_simp; ring
    rw [this, le_div_iff₀ (by positivity)]
    linarith
  have hlow : ∀ᶠ n in atTop, u n - K / n ≤ f n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    rw [hfeq, Nat.cast_choose_two, hu]
    have hpos : (0 : ℝ) < n * (n - 1) := by nlinarith
    have hn1 : (n : ℝ) + -1 ≠ 0 := by linarith
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hT := turanNumber_lower_bound hr n
    rw [le_div_iff₀ (by positivity)]
    have : (L * ((n : ℝ) / ((n : ℝ) + -1)) - K / n) * ((n : ℝ) * (n - 1) / 2) =
        (((r : ℝ) - 1) * ((n : ℝ) ^ 2 - (r : ℝ) ^ 2) + ((r : ℝ) - 1) * r ^ 2 -
          ((r : ℝ) - 1) * r * r * (n - 1)) / (2 * r) := by
      simp only [L, K]; field_simp; ring
    rw [this, div_le_iff₀ (by positivity)]
    have hk : 0 ≤ ((r : ℝ) - 1) * r ^ 2 * (n - 2) := by
      have : (0 : ℝ) ≤ r - 1 := by linarith
      have : (0 : ℝ) ≤ n - 2 := by linarith
      positivity
    nlinarith
  have hu_lim : Tendsto u atTop (𝓝 L) := by
    have := (tendsto_natCast_div_add_atTop (𝕜 := ℝ) (-1)).const_mul L
    simpa [hu] using this
  have hl_lim : Tendsto (fun n => u n - K / n) atTop (𝓝 L) := by
    simpa using hu_lim.sub (tendsto_const_div_atTop_nhds_zero_nat K)
  have hf_lim : Tendsto f atTop (𝓝 L) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hl_lim hu_lim hlow hup
  exact tendsto_nhds_unique (tendsto_turanDensity _) hf_lim

end MathlibExt.Combinatorics.SimpleGraph.TuranDensityComplete

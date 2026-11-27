/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.MaynardVariationalBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Tests for `M₅ > 2`, `M₁₀₅ > 4` and the growth bound
-/

namespace MathlibExtTest.NumberTheory.MaynardVariationalBounds

open Filter Topology MathlibExt.NumberTheory.GPYMaynard
open WantedExt.NumberTheory.MaynardVariationalBounds

example : 2 < maynardM 5 := two_lt_maynardM_five

/-- Maynard's strict bound leaves room for a level `θ = 1 - ε` below `1`, as required when
applying the Elliott–Halberstam conjecture. The threshold `ρ = 1` is still satisfied. -/
example : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ 1 < (1 - ε) * maynardM 5 / 2 := by
  have hM : 0 < maynardM 5 := lt_trans (by norm_num) two_lt_maynardM_five
  have h : (2 : ℝ) / maynardM 5 < 1 :=
    (div_lt_iff₀ hM).2 (by simpa using two_lt_maynardM_five)
  obtain ⟨θ, hθ, hθ1⟩ := exists_between h
  have hθ0 : 0 < θ := (div_pos (by norm_num) hM).trans hθ
  have hprod : (2 : ℝ) < θ * maynardM 5 := (div_lt_iff₀ hM).1 hθ
  refine ⟨1 - θ, sub_pos.mpr hθ1, sub_lt_self _ hθ0, ?_⟩
  rw [sub_sub_cancel]
  linarith

example : 4 < maynardM 105 := four_lt_maynardM_105

/-- With the Bombieri–Vinogradov level `θ = 1/2`, the condition `ρ < θ M₁₀₅ / 2` of Maynard's
reduction holds for `ρ = 1`, that is two primes among the translates. -/
example : (1 : ℝ) < 1 / 2 * maynardM 105 / 2 := by
  have h := four_lt_maynardM_105
  linarith

/-- Under the Elliott–Halberstam level `θ = 1`, the condition holds for `ρ = 2`. -/
example : (2 : ℝ) < 1 * maynardM 105 / 2 := by
  have h := four_lt_maynardM_105
  linarith

/-- The strict inequality leaves room for a level `θ = 1/2 - ε` just below `1/2`, which is what
the Bombieri–Vinogradov theorem provides. -/
example : ∃ ε > (0 : ℝ), 1 < (1 / 2 - ε) * maynardM 105 / 2 := by
  have h := four_lt_maynardM_105
  refine ⟨(maynardM 105 - 4) / (4 * maynardM 105), div_pos (by linarith) (by linarith), ?_⟩
  have e : (1 / 2 - (maynardM 105 - 4) / (4 * maynardM 105)) * maynardM 105 / 2 =
      (maynardM 105 + 4) / 8 := by
    field_simp
    ring
  rw [e]
  linarith

/-- `M₁₀₅ > 4` discharges the threshold hypothesis of Maynard's reduction for `105` shifts at the
level `θ = 1/2` with `ρ = 1`: the asymptotics of the sieve sums then give infinitely many `n` with
at least two of the `n + h` prime. -/
example (H : Finset ℕ) (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hasym : ∀ F, IsMaynardProfile 105 F → ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ (w : ℕ → ℕ → ℝ) (B : ℕ → ℝ),
      (∀ N n, 0 ≤ w N n) ∧ (∀ᶠ N in atTop, 0 < B N) ∧
      Tendsto (fun N => (∑ n ∈ Finset.Ico N (2 * N), w N n) / B N) atTop
        (𝓝 (maynardI 105 F)) ∧
      Tendsto (fun N => (∑ n ∈ Finset.Ico N (2 * N),
        (primeShiftCount H n : ℝ) * w N n) / B N) atTop
        (𝓝 ((1 / 2 / 2 - δ) * ∑ m, maynardJ 105 m F))) :
    {n : ℕ | (1 : ℝ) < primeShiftCount H n}.Infinite :=
  infinite_lt_primeShiftCount_of_lt_maynardM H 105 (1 / 2) 1 (by norm_num)
    (by linarith [four_lt_maynardM_105]) δ₀ hδ₀ hasym

/-- The growth bound holds at an index at least `105`. -/
example : ∃ k : ℕ, 105 ≤ k ∧
    Real.log k - 2 * Real.log (Real.log k) - 2 < maynardM k := by
  obtain ⟨K, hK⟩ :=
    WantedExt.NumberTheory.MaynardVariationalBounds.eventually_log_sub_lt_maynardM
  exact ⟨max K 105, le_max_right _ _, hK _ (le_max_left _ _)⟩

end MathlibExtTest.NumberTheory.MaynardVariationalBounds

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Classical.ViabilityRegimes
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum

@[expose] public section

open Filter Topology Set
open MathlibExt.Biology.PopulationGenetics.Selection
open MathlibExt.Biology.PopulationGenetics.Classical.ViabilityRegimes

namespace MathlibExtTest.Biology.PopulationGenetics.Classical.ViabilityRegimes

/-! ### One generation, computed directly -/

/-- With viabilities `1 : 1 : 0` (recessive lethal `aa`) and `p = 1/2`, the mean viability is
`3/4` and one generation gives `p' = (1/4 + 1/4) / (3/4) = 2/3`. -/
example : diploidSelect ![1 / 2, 1 - 1 / 2] ![![1, 1], ![1, 0]] 0 = 2 / 3 ∧
    diploidMeanFitness ![1 / 2, 1 - 1 / 2] ![![(1 : ℝ), 1], ![1, 0]] = 3 / 4 := by
  norm_num [diploidSelect, marginalFitness, diploidMeanFitness, Fin.sum_univ_two]

/-- The same step through the change formula of `viability_selection_regimes`:
`p' - p = p q (p (wAA - wAa) + q (wAa - waa)) / w̄`. -/
example :
    diploidSelect ![1 / 2, 1 - 1 / 2] ![![1, 1], ![1, 0]] 0 - 1 / 2 =
      1 / 2 * (1 - 1 / 2) * (1 / 2 * ((1 : ℝ) - 1) + (1 - 1 / 2) * (1 - 0)) /
        diploidMeanFitness ![1 / 2, 1 - 1 / 2] ![![(1 : ℝ), 1], ![1, 0]] :=
  (viability_selection_regimes 1 1 0 (p₀ := 1 / 2) ⟨by norm_num, by norm_num⟩).1 (1 / 2)
    (by norm_num [diploidMeanFitness, Fin.sum_univ_two])

/-! ### Directional selection -/

/-- Additive viabilities `1 : 1/2 : 0`: from `p₀ = 1/10` the frequency of `A` increases strictly
to `1`, staying in `(0, 1)`. -/
example :
    let f : ℝ → ℝ := fun p => diploidSelect ![p, 1 - p] ![![1, 1 / 2], ![1 / 2, 0]] 0
    (∀ n, f^[n] (1 / 10) ∈ Ioo 0 1) ∧ StrictMono (fun n => f^[n] (1 / 10)) ∧
      Tendsto (fun n => f^[n] (1 / 10)) atTop (𝓝 1) := by
  intro f
  obtain ⟨-, hdir, -⟩ := viability_selection_regimes 1 (1 / 2) 0 (p₀ := 1 / 10)
    ⟨by norm_num, by norm_num⟩
  exact (hdir le_rfl (by norm_num) (by norm_num) (by norm_num)).2.2.1 (by norm_num)

/-- Boundary case `wAa = waa = 0`: only `AA` survives, so the frequency of `A` jumps to `1` in one
generation; strict increase inside `(0, 1)` needs `wAa > 0`. -/
example : diploidSelect ![1 / 3, 1 - 1 / 3] ![![1, 0], ![0, 0]] 0 = 1 := by
  obtain ⟨-, hdir, -⟩ := viability_selection_regimes 1 0 0 (p₀ := 1 / 3) ⟨by norm_num, by norm_num⟩
  exact (hdir le_rfl le_rfl (by norm_num) (by norm_num)).2.2.2 rfl rfl

/-! ### Overdominance -/

/-- Felsenstein's overdominant example (fitnesses `0.85 : 1 : 0.7`, so `s = 0.15`, `t = 0.3` and
`p_e = 2/3`): from `p₀ = 0.01` the frequency of `A` increases monotonically to `2/3` without
exceeding it. -/
example :
    let f : ℝ → ℝ := fun p => diploidSelect ![p, 1 - p] ![![17 / 20, 1], ![1, 7 / 10]] 0
    Monotone (fun n => f^[n] (1 / 100)) ∧ (∀ n, f^[n] (1 / 100) ≤ 2 / 3) ∧
      Tendsto (fun n => f^[n] (1 / 100)) atTop (𝓝 (2 / 3)) := by
  intro f
  obtain ⟨-, -, h⟩ := viability_selection_regimes (17 / 20) 1 (7 / 10) (p₀ := 1 / 100)
    ⟨by norm_num, by norm_num⟩
  obtain ⟨-, -, hod, -⟩ := h (3 / 20) (3 / 10) (by norm_num) rfl (by norm_num)
  obtain ⟨-, -, -, -, -, hmono, -, hlim⟩ :=
    hod (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hpe : (3 / 10 : ℝ) / (3 / 20 + 3 / 10) = 2 / 3 := by norm_num
  rw [hpe] at hmono hlim
  exact ⟨(hmono (by norm_num)).1, (hmono (by norm_num)).2, hlim⟩

/-- The same example from `p₀ = 0.99`: the frequency of `A` decreases to `2/3`, staying above it. -/
example :
    let f : ℝ → ℝ := fun p => diploidSelect ![p, 1 - p] ![![17 / 20, 1], ![1, 7 / 10]] 0
    Antitone (fun n => f^[n] (99 / 100)) ∧ (∀ n, 2 / 3 ≤ f^[n] (99 / 100)) := by
  intro f
  obtain ⟨-, -, h⟩ := viability_selection_regimes (17 / 20) 1 (7 / 10) (p₀ := 99 / 100)
    ⟨by norm_num, by norm_num⟩
  obtain ⟨-, -, hod, -⟩ := h (3 / 20) (3 / 10) (by norm_num) rfl (by norm_num)
  obtain ⟨-, -, -, -, -, -, hanti, -⟩ :=
    hod (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hpe : (3 / 10 : ℝ) / (3 / 20 + 3 / 10) = 2 / 3 := by norm_num
  rw [hpe] at hanti
  exact hanti (by norm_num)

/-- Boundary case `s = t = 1` (both homozygotes lethal): the factor `p q (s + t) / w̄` equals `1`
and the population reaches `p_e = 1/2` in one generation. -/
example : diploidSelect ![1 / 10, 1 - 1 / 10] ![![0, 1], ![1, 0]] 0 = 1 / 2 := by
  obtain ⟨-, -, h⟩ := viability_selection_regimes 0 1 0 (p₀ := 1 / 10) ⟨by norm_num, by norm_num⟩
  obtain ⟨-, -, hod, -⟩ := h 1 1 (by norm_num) rfl (by norm_num)
  obtain ⟨-, -, -, -, hone, -⟩ := hod one_pos le_rfl one_pos le_rfl
  have := hone rfl rfl
  norm_num at this ⊢
  exact this

/-- The interior equilibrium of the example is a fixed point, and `1/2` is not. -/
example :
    diploidSelect ![2 / 3, 1 - 2 / 3] ![![17 / 20, 1], ![1, 7 / 10]] 0 = 2 / 3 ∧
      diploidSelect ![1 / 2, 1 - 1 / 2] ![![17 / 20, 1], ![1, 7 / 10]] 0 ≠ 1 / 2 := by
  norm_num [diploidSelect, marginalFitness, diploidMeanFitness, Fin.sum_univ_two]

/-! ### Underdominance -/

/-- Felsenstein's underdominant example (fitnesses `1.15 : 1 : 1.3`, so `s = -0.15`, `t = -0.3`
and `p_e = 2/3`): below `p_e` the frequency of `A` tends to `0`, above it to `1`. -/
example :
    let f : ℝ → ℝ := fun p => diploidSelect ![p, 1 - p] ![![23 / 20, 1], ![1, 13 / 10]] 0
    Tendsto (fun n => f^[n] (3 / 5)) atTop (𝓝 0) ∧
      Tendsto (fun n => f^[n] (7 / 10)) atTop (𝓝 1) := by
  intro f
  obtain ⟨-, -, h₁⟩ := viability_selection_regimes (23 / 20) 1 (13 / 10) (p₀ := 3 / 5)
    ⟨by norm_num, by norm_num⟩
  obtain ⟨-, -, h₂⟩ := viability_selection_regimes (23 / 20) 1 (13 / 10) (p₀ := 7 / 10)
    ⟨by norm_num, by norm_num⟩
  obtain ⟨-, -, -, hud₁⟩ := h₁ (-3 / 20) (-3 / 10) (by norm_num) rfl (by norm_num)
  obtain ⟨-, -, -, hud₂⟩ := h₂ (-3 / 20) (-3 / 10) (by norm_num) rfl (by norm_num)
  obtain ⟨-, -, hlow, -⟩ := hud₁ (by norm_num) (by norm_num)
  obtain ⟨-, -, -, hhigh, -⟩ := hud₂ (by norm_num) (by norm_num)
  exact ⟨hlow (by norm_num), hhigh (by norm_num)⟩

/-- Started exactly at the unstable equilibrium `p_e = 2/3`, the population stays there. -/
example :
    let f : ℝ → ℝ := fun p => diploidSelect ![p, 1 - p] ![![23 / 20, 1], ![1, 13 / 10]] 0
    ∀ n, f^[n] (2 / 3) = 2 / 3 := by
  intro f
  obtain ⟨-, -, h⟩ := viability_selection_regimes (23 / 20) 1 (13 / 10) (p₀ := 2 / 3)
    ⟨by norm_num, by norm_num⟩
  obtain ⟨-, -, -, hud⟩ := h (-3 / 20) (-3 / 10) (by norm_num) rfl (by norm_num)
  obtain ⟨-, -, -, -, hfix⟩ := hud (by norm_num) (by norm_num)
  have hpe : (-3 / 10 : ℝ) / (-3 / 20 + -3 / 10) = 2 / 3 := by norm_num
  rw [hpe] at hfix
  exact hfix rfl

end MathlibExtTest.Biology.PopulationGenetics.Classical.ViabilityRegimes

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Simulation.SelectBest
import Mathlib.Probability.Distributions.Bernoulli

open MeasureTheory ProbabilityTheory Real

namespace Cslib.Algorithms.Simulation.SelectBest

/-! Common random numbers: every alternative is evaluated on the same independent inputs
`U₁, …, Uₙ`, so the replications of different alternatives are dependent. The bound only uses the
independence of the replications of each alternative. -/

example {Ω X : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype X]
    [Nonempty X] {n : ℕ} {U : Fin n → Ω → ℝ} (hU : iIndepFun U μ)
    (hUm : ∀ i, Measurable (U i)) {g : X → ℝ → ℝ} (hg : ∀ x, Measurable (g x))
    (hg01 : ∀ x u, g x u ∈ Set.Icc (0 : ℝ) 1) {C : X → ℝ}
    (hC : ∀ x i, μ[fun ω => g x (U i ω)] = C x) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ Finset.univ.sup' Finset.univ_nonempty
        fun x => |(1 / n : ℝ) * ∑ i, g x (U i ω) - C x|} ≤
      2 * Fintype.card X * exp (-2 * n * ε ^ 2) := by
  have h := (measureReal_sup'_abs_avg_sub_ge_le_and_sub_inf'_lt
    (Y := fun x i ω => g x (U i ω)) (fun x => hU.comp (fun _ => g x) fun _ => hg x)
    (fun x i => ((hg x).comp (hUm i)).aemeasurable)
    (fun x i => Filter.Eventually.of_forall fun ω => hg01 x (U i ω)) hC hε).1
  simpa using h

/-! Fair coin flips: `n` independent fair coins `ω : Fin n → Bool`, and alternatives whose
`i`-th replication is `f x (ω i)` for a payoff `f x : Bool → [0, 1]`. -/

/-- The probability `1/2`. -/
private noncomputable abbrev half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

/-- `n` independent fair coin flips. -/
private noncomputable abbrev coins (n : ℕ) : Measure (Fin n → Bool) :=
  Measure.pi fun _ => bernoulliMeasure true false half

private theorem integral_coins (n : ℕ) (f : Bool → ℝ) (i : Fin n) :
    ∫ ω, f (ω i) ∂coins n = (f true + f false) / 2 := by
  have hmp := measurePreserving_eval (fun _ : Fin n => bernoulliMeasure true false half) i
  rw [← integral_map (measurable_pi_apply i).aemeasurable
    (Measurable.of_discrete (f := f)).aestronglyMeasurable, hmp.map_eq,
    integral_bernoulliMeasure]
  simp only [smul_eq_mul]
  norm_num
  ring

/-- The theorem for alternatives evaluated on common fair coin flips. -/
private theorem coins_bound {X : Type*} [Fintype X] [Nonempty X] {n : ℕ} (f : X → Bool → ℝ)
    (hf : ∀ x b, f x b ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 ≤ ε) :
    (coins n).real {ω | ε ≤ Finset.univ.sup' Finset.univ_nonempty
        fun x => |(1 / n : ℝ) * ∑ i, f x (ω i) - (f x true + f x false) / 2|} ≤
      2 * Fintype.card X * exp (-2 * n * ε ^ 2) ∧
    ∀ ω : Fin n → Bool, Finset.univ.sup' Finset.univ_nonempty
        (fun x => |(1 / n : ℝ) * ∑ i, f x (ω i) - (f x true + f x false) / 2|) < ε →
      ∀ xhat, (∀ x, (1 / n : ℝ) * ∑ i, f xhat (ω i) ≤ (1 / n : ℝ) * ∑ i, f x (ω i)) →
        (f xhat true + f xhat false) / 2 -
          Finset.univ.inf' Finset.univ_nonempty (fun x => (f x true + f x false) / 2) <
          2 * ε := by
  have h := measureReal_sup'_abs_avg_sub_ge_le_and_sub_inf'_lt
    (μ := coins n) (Y := fun x i ω => f x (ω i))
    (fun x => iIndepFun_pi (X := fun _ (b : Bool) => f x b) fun _ =>
      (Measurable.of_discrete (f := f x)).aemeasurable)
    (fun x i => ((Measurable.of_discrete (f := f x)).comp (measurable_pi_apply i)).aemeasurable)
    (fun x i => Filter.Eventually.of_forall fun ω => hf x (ω i))
    (fun x i => integral_coins n (f x) i) hε
  simpa using h

/-- An antithetic pair: alternative `true` pays the coin and alternative `false` pays one minus
the coin, so for `n > 0` their estimates always sum to `1` (for `n = 0` both are `0`); both have
mean `1/2`. The bound holds for every `n`. -/
example (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (coins n).real {ω | ε ≤ Finset.univ.sup' Finset.univ_nonempty
        fun x : Bool => |(1 / n : ℝ) * ∑ i, (if ω i = x then 1 else 0) - 1 / 2|} ≤
      4 * exp (-2 * n * ε ^ 2) := by
  have h := (coins_bound (n := n) (fun x b => if b = x then (1 : ℝ) else 0)
    (fun x b => by split_ifs <;> norm_num) hε).1
  have hmean : ∀ x : Bool,
      ((if true = x then (1 : ℝ) else 0) + (if false = x then 1 else 0)) / 2 = 1 / 2 := by
    intro x; cases x <;> norm_num
  simp only [hmean, Fintype.card_bool] at h
  linarith

/-- Selecting the better of a fair coin (mean `1/2`) and a constant `3/4`: whenever both
estimates are within `1/8` of their means, every alternative with the smallest estimate is the
coin. The uniform bound puts the probability of the contrary below `4 exp (-n / 32)`. -/
example (n : ℕ) (ω : Fin n → Bool)
    (hω : Finset.univ.sup' Finset.univ_nonempty
      (fun x : Bool => |(1 / n : ℝ) * ∑ i, (if x then (if ω i then 1 else 0) else 3 / 4) -
        (if x then 1 / 2 else 3 / 4)|) < 1 / 8)
    (xhat : Bool)
    (hmin : ∀ x : Bool, (1 / n : ℝ) * ∑ i, (if xhat then (if ω i then 1 else 0) else 3 / 4) ≤
      (1 / n : ℝ) * ∑ i, (if x then (if ω i then 1 else 0) else 3 / 4)) :
    xhat = true := by
  let f : Bool → Bool → ℝ := fun x b => if x then (if b then 1 else 0) else 3 / 4
  have hmean : ∀ x, (f x true + f x false) / 2 = if x then 1 / 2 else 3 / 4 := by
    intro x; cases x <;> norm_num [f]
  have hω' : Finset.univ.sup' Finset.univ_nonempty
      (fun x => |(1 / n : ℝ) * ∑ i, f x (ω i) - (f x true + f x false) / 2|) < 1 / 8 := by
    simp only [hmean]
    exact hω
  have h := (coins_bound (n := n) f (fun x b => by cases x <;> cases b <;> norm_num [f])
    (ε := 1 / 8) (by norm_num)).2 ω hω' xhat hmin
  have hinf : Finset.univ.inf' Finset.univ_nonempty (fun x => (f x true + f x false) / 2) =
      1 / 2 := by
    simp only [hmean]
    apply le_antisymm
    · exact Finset.inf'_le _ (Finset.mem_univ true) |>.trans (by norm_num)
    · exact Finset.le_inf' _ _ fun x _ => by cases x <;> norm_num
  rw [hinf, hmean] at h
  cases xhat
  · norm_num at h
  · rfl

/-- The bound with no replications: the estimates are `0` and the right-hand side is
`2 |X| ≥ 1`. -/
example {Ω X : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype X]
    [Nonempty X] {Y : X → Fin 0 → Ω → ℝ} {C : X → ℝ} {a b ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ Finset.univ.sup' Finset.univ_nonempty
        fun x => |(1 / (0 : ℕ) : ℝ) * ∑ i, Y x i ω - C x|} ≤
      2 * Fintype.card X * exp (-2 * (0 : ℕ) * ε ^ 2 / (b - a) ^ 2) :=
  (measureReal_sup'_abs_avg_sub_ge_le_and_sub_inf'_lt (fun _ => iIndepFun.of_subsingleton)
    (fun _ i => i.elim0) (fun _ i => i.elim0) (fun _ i => i.elim0) hε).1

/-! The replications are only almost-everywhere measurable, so the deviation event need not be
measurable; it is null-measurable, so its `μ.real` is its probability in the completion of `μ`. -/

example {Ω X : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype X] [Nonempty X] {n : ℕ}
    {Y : X → Fin n → Ω → ℝ} (hmeas : ∀ x i, AEMeasurable (Y x i) μ) (C : X → ℝ) (ε : ℝ) :
    NullMeasurableSet {ω | ε ≤ Finset.univ.sup' Finset.univ_nonempty
      fun x => |(1 / n : ℝ) * ∑ i, Y x i ω - C x|} μ := by
  have hdev : ∀ x, AEMeasurable (fun ω => |(1 / n : ℝ) * ∑ i, Y x i ω - C x|) μ := by
    intro x
    have := hmeas x
    fun_prop
  have hsup : AEMeasurable (Finset.univ.sup' Finset.univ_nonempty
      fun x ω => |(1 / n : ℝ) * ∑ i, Y x i ω - C x|) μ :=
    Finset.sup'_induction (p := fun f => AEMeasurable f μ) _ _ (fun _ hf _ hg => hf.sup hg)
      fun x _ => hdev x
  refine nullMeasurableSet_le aemeasurable_const ?_
  convert hsup using 1
  ext ω
  simp only [Finset.sup'_apply]

/-! The set of alternatives is nonempty: the maximum and the minimum over it must exist. The
theorem applies with a `Nonempty X` instance and fails to apply without one; only the failure is
checked, not Lean's message. -/

example {Ω X : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype X]
    [Nonempty X] {Y : X → Fin 1 → Ω → ℝ} {C : X → ℝ} (h_indep : ∀ x, iIndepFun (Y x) μ)
    (hmeas : ∀ x i, AEMeasurable (Y x i) μ) (hY : ∀ x i, ∀ᵐ ω ∂μ, Y x i ω ∈ Set.Icc (0 : ℝ) 1)
    (hC : ∀ x i, μ[Y x i] = C x) :=
  measureReal_sup'_abs_avg_sub_ge_le_and_sub_inf'_lt h_indep hmeas hY hC le_rfl

#guard_msgs (drop info) in
#check_failure fun (Ω X : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype X] (Y : X → Fin 1 → Ω → ℝ) (C : X → ℝ) (h_indep : ∀ x, iIndepFun (Y x) μ)
    (hmeas : ∀ x i, AEMeasurable (Y x i) μ) (hY : ∀ x i, ∀ᵐ ω ∂μ, Y x i ω ∈ Set.Icc (0 : ℝ) 1)
    (hC : ∀ x i, μ[Y x i] = C x) =>
  measureReal_sup'_abs_avg_sub_ge_le_and_sub_inf'_lt h_indep hmeas hY hC le_rfl

end Cslib.Algorithms.Simulation.SelectBest

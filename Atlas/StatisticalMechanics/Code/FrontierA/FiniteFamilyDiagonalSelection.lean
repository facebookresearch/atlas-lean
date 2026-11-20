/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib









open Filter Topology
open scoped BigOperators

namespace StatMech.FrontierA

theorem exists_diagonal_close_on_finiteFamilies_of_pos
    {α : Type*} [DecidableEq α]
    (f : α → Nat → Real) (limit : α → Real)
    (hf : ∀ a, Tendsto (f a) atTop (nhds (limit a)))
    (family : Nat → Finset α) (epsilon : Nat → Real)
    (hepsilon : ∀ n, 0 < epsilon n) :
    ∃ scale : Nat → Nat,
      Tendsto scale atTop atTop ∧
      ∀ n a, a ∈ family n →
        |f a (scale n) - limit a| < epsilon n := by
  have hfamily (n : Nat) :
      ∀ᶠ k : Nat in atTop, ∀ a ∈ family n,
        |f a k - limit a| < epsilon n := by
    rw [Filter.eventually_all_finset (family n)]
    intro a ha
    obtain ⟨N, hN⟩ :=
      (Metric.tendsto_atTop.1 (hf a)) _ (hepsilon n)
    filter_upwards [eventually_ge_atTop N] with k hk
    simpa only [Real.dist_eq] using hN k hk
  have hexists (n : Nat) :
      ∃ k : Nat, n ≤ k ∧ ∀ a ∈ family n,
        |f a k - limit a| < epsilon n := by
    exact ((eventually_ge_atTop n).and (hfamily n)).exists
  choose scale hscale using hexists
  refine ⟨scale, tendsto_atTop_mono (fun n => (hscale n).1) tendsto_id, ?_⟩
  intro n a ha
  exact (hscale n).2 a ha

theorem exists_diagonal_close_on_finiteFamilies
    {α : Type*} [DecidableEq α]
    (f : α → Nat → Real) (limit : α → Real)
    (hf : ∀ a, Tendsto (f a) atTop (nhds (limit a)))
    (family : Nat → Finset α) :
    ∃ scale : Nat → Nat,
      Tendsto scale atTop atTop ∧
      ∀ n a, a ∈ family n →
        |f a (scale n) - limit a| < 1 / (n + 1 : Real) := by
  apply exists_diagonal_close_on_finiteFamilies_of_pos f limit hf family
  intro n
  positivity

theorem exists_diagonal_weightedSum_close_on_finiteFamilies
    {α : Type*} [DecidableEq α]
    (f : α → Nat → Real) (limit : α → Real)
    (hf : ∀ a, Tendsto (f a) atTop (nhds (limit a)))
    (family : Nat → Finset α) (weight : Nat → α → Real)
    (epsilon : Nat → Real) (hepsilon : ∀ n, 0 < epsilon n) :
    ∃ scale : Nat → Nat,
      Tendsto scale atTop atTop ∧
      ∀ n,
        abs ((∑ a ∈ family n, weight n a * f a (scale n)) -
          (∑ a ∈ family n, weight n a * limit a)) < epsilon n := by
  let mass : Nat → Real := fun n => ∑ a ∈ family n, |weight n a|
  let pointError : Nat → Real := fun n => epsilon n / (mass n + 1)
  have hmass (n : Nat) : 0 ≤ mass n := by
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hpointError (n : Nat) : 0 < pointError n := by
    exact div_pos (hepsilon n) (by dsimp [mass]; positivity)
  obtain ⟨scale, hscale, hclose⟩ :=
    exists_diagonal_close_on_finiteFamilies_of_pos
      f limit hf family pointError hpointError
  refine ⟨scale, hscale, fun n => ?_⟩
  calc
    abs ((∑ a ∈ family n, weight n a * f a (scale n)) -
        (∑ a ∈ family n, weight n a * limit a)) =
        abs (∑ a ∈ family n,
          (weight n a * f a (scale n) - weight n a * limit a)) := by
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ a ∈ family n,
        |weight n a * f a (scale n) - weight n a * limit a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ family n, |weight n a| * pointError n := by
      apply Finset.sum_le_sum
      intro a ha
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hclose n a ha).le (abs_nonneg _)
    _ = mass n * pointError n := by
      rw [Finset.sum_mul]
    _ < epsilon n := by
      dsimp [pointError]
      have hden : 0 < mass n + 1 := by linarith [hmass n]
      rw [← mul_div_assoc, div_lt_iff₀ hden]
      nlinarith [hepsilon n, hmass n]

end StatMech.FrontierA

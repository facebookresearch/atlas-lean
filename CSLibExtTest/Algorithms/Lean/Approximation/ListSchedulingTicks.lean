/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Approximation.ListSchedulingTicks
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Tests for rounding processing times to ticks -/

namespace Cslib.Algorithms.Lean.Scheduling

-- The same processing time appears 100 times: rounding is per occurrence, not per distinct time.
example :
    let σ : Fin 1 → List ℝ := fun _ => List.replicate 100 (1 / 100)
    (Finset.univ.sup' Finset.univ_nonempty fun i => (σ i).sum) = 1 ∧
      (1 : ℝ) * (makespan (fun i => (σ i).map fun p => ⌈p / 1⌉₊) : ℝ) = 100 := by
  dsimp only
  have hceil : ⌈(1 / 100 : ℝ)⌉₊ = 1 :=
    Nat.le_antisymm (Nat.ceil_le.mpr (by norm_num))
      (Nat.succ_le_of_lt (Nat.lt_ceil.mpr (by norm_num)))
  constructor
  · norm_num [Finset.sup'_const, List.sum_replicate, nsmul_eq_mul]
  · simp only [one_mul, makespan, div_one, List.map_replicate, hceil,
      Finset.sup_const Finset.univ_nonempty, List.sum_replicate, nsmul_eq_mul]
    norm_num

-- An idle machine and a machine with one zero-duration job both have load zero.
example :
    let σ : Fin 2 → List ℝ := fun i => if i = 0 then [0] else []
    let C := Finset.univ.sup' Finset.univ_nonempty fun i => (σ i).sum
    let T := makespan fun i => (σ i).map fun p => ⌈p / (1 / 2)⌉₊
    C = 0 ∧ T = 0 := by
  intro σ C T
  have hT : T = 0 := by
    apply Nat.le_zero.mp
    apply Finset.sup_le
    intro i _
    by_cases hi : i = 0 <;> simp [σ, hi]
  have hσ : ∀ i, ∀ p ∈ σ i, 0 ≤ p := by
    intro i p hp
    by_cases hi : i = 0 <;> simp_all [σ]
  have h := (makespan_rounding_to_ticks_bounds σ (δ := 1 / 2) (by norm_num) hσ).1
  change C ≤ (1 / 2 : ℝ) * (T : ℝ) at h
  rw [hT, Nat.cast_zero, mul_zero] at h
  refine ⟨le_antisymm h ?_, hT⟩
  have h₀ := Finset.le_sup' (fun i => (σ i).sum) (Finset.mem_univ (0 : Fin 2))
  simpa [σ] using h₀

-- The second machine maximizes real load, but the first maximizes tick load.
-- Using just the second machine's job count would not give a valid upper bound.
example :
    let σ : Fin 2 → List ℝ := fun i => if i = 0 then [1 / 5, 1 / 5, 1 / 5] else [9 / 10]
    let C := Finset.univ.sup' Finset.univ_nonempty fun i => (σ i).sum
    let T := makespan fun i => (σ i).map fun p => ⌈p / (1 / 2)⌉₊
    let K := Finset.univ.sup fun i => (σ i).length
    C = 9 / 10 ∧ T = 3 ∧ K = 3 ∧
      (1 / 2 : ℝ) * (T : ℝ) ≤ C + (1 / 2 : ℝ) * (K : ℝ) ∧
      ¬ (1 / 2 : ℝ) * (T : ℝ) ≤ C + (1 / 2 : ℝ) * ((σ 1).length : ℝ) := by
  intro σ C T K
  have hceil₀ : ⌈(1 / 5 : ℝ) / (1 / 2)⌉₊ = 1 :=
    Nat.le_antisymm (Nat.ceil_le.mpr (by norm_num))
      (Nat.succ_le_of_lt (Nat.lt_ceil.mpr (by norm_num)))
  have hceil₁ : ⌈(9 / 10 : ℝ) / (1 / 2)⌉₊ = 2 :=
    Nat.le_antisymm (Nat.ceil_le.mpr (by norm_num))
      (Nat.succ_le_of_lt (Nat.lt_ceil.mpr (by norm_num)))
  have hC : C = 9 / 10 := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      fin_cases i <;> norm_num [σ, List.sum_cons]
    · have h := Finset.le_sup' (fun i => (σ i).sum) (Finset.mem_univ (1 : Fin 2))
      change (σ 1).sum ≤ C at h
      have hnine : (σ 1).sum = 9 / 10 := by norm_num [σ, List.sum_cons]
      rwa [hnine] at h
  let ticks : Fin 2 → List ℕ := fun i => (σ i).map fun p => ⌈p / (1 / 2)⌉₊
  have hticks₀ : (ticks 0).sum = 3 := by
    change ⌈(1 / 5 : ℝ) / (1 / 2)⌉₊ +
      (⌈(1 / 5 : ℝ) / (1 / 2)⌉₊ + (⌈(1 / 5 : ℝ) / (1 / 2)⌉₊ + 0)) = 3
    rw [hceil₀]
  have hticks₁ : (ticks 1).sum = 2 := by
    change ⌈(9 / 10 : ℝ) / (1 / 2)⌉₊ + 0 = 2
    rw [hceil₁]
  have hT : T = 3 := by
    change Finset.univ.sup (fun i => (ticks i).sum) = 3
    apply le_antisymm
    · apply Finset.sup_le
      intro i _
      fin_cases i
      · exact hticks₀.le
      · exact hticks₁.le.trans (by decide)
    · have h := Finset.le_sup (s := Finset.univ) (f := fun i => (ticks i).sum)
          (Finset.mem_univ (0 : Fin 2))
      rwa [hticks₀] at h
  have hK : K = 3 := by
    change Finset.univ.sup (fun i => (σ i).length) = 3
    apply le_antisymm
    · apply Finset.sup_le
      intro i _
      fin_cases i <;> norm_num [σ]
    · have h := Finset.le_sup (s := Finset.univ) (f := fun i => (σ i).length)
          (Finset.mem_univ (0 : Fin 2))
      have hlen : (σ 0).length = 3 := by simp [σ]
      rwa [hlen] at h
  have hσ : ∀ i, ∀ p ∈ σ i, 0 ≤ p := by
    intro i p hp
    fin_cases i <;> simp [σ] at hp <;> subst p <;> norm_num
  refine ⟨hC, hT, hK, (makespan_rounding_to_ticks_bounds σ (δ := 1 / 2) (by norm_num) hσ).2, ?_⟩
  norm_num [hC, hT, σ]

end Cslib.Algorithms.Lean.Scheduling

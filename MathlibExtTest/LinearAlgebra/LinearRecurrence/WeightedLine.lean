/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
The exact-source consumer restates the theorem wrapper
Theorems/
Thm_Polynomial_shellRecurrent_finsum_line_of_separatedRational_of_shellRecurrence.lean
from Fermat's Last Theorem in Lean 4, revision
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright 2026 Anthropic, PBC. Apache License, Version 2.0.
The published source names no individual author. Applications and boundary
proofs here are new, not copied from another candidate or diagnostic reviewer.
-/
module

public import MathlibExt.LinearAlgebra.LinearRecurrence.WeightedLine
public import MathlibExt.NumberTheory.Recurrences.CRecursiveExponentialGrowth
public import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.Polynomial.Degree.Domain

open scoped BigOperators
open Polynomial

public section

noncomputable section

namespace WeightedLineTest

/-- The literal source interface, including all redundant hypotheses. -/
theorem exact_source
    (A : ℤ × ℤ → ℂ) (b : ℤ → ℂ) (α β : ℂ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (e₁ e₂ : ℕ) (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (hA : ∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ),
      D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
      (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0) ∧
      (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
        ∑ i ∈ Finset.range (D₁.natDegree + 1),
          ∑ l ∈ Finset.range (D₂.natDegree + 1),
            D₁.coeff i * D₂.coeff l *
              A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0))
    (hb : ∃ (N₂ : ℤ) (E : Polynomial ℂ) (M' : ℕ), E.eval 0 ≠ 0 ∧
      (∀ m : ℤ, m < N₂ → b m = 0) ∧
      (∀ m : ℕ, M' ≤ m → ∑ i ∈ Finset.range (E.natDegree + 1),
        E.coeff i * b (N₂ + (m : ℤ) - (i : ℤ)) = 0)) :
    ∃ (N : ℤ) (E : Polynomial ℂ) (M : ℕ), E.eval 0 ≠ 0 ∧
      (∀ m : ℤ, m < N → (fun t : ℤ => ∑ᶠ n : ℤ × ℤ,
        if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then
          A n * b n.1 * α ^ n.1 * β ^ n.2 else 0) m = 0) ∧
      (∀ m : ℕ, M ≤ m → ∑ i ∈ Finset.range (E.natDegree + 1),
        E.coeff i * (fun t : ℤ => ∑ᶠ n : ℤ × ℤ,
          if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then
            A n * b n.1 * α ^ n.1 * β ^ n.2 else 0)
          (N + (m : ℤ) - (i : ℤ)) = 0) :=
  exists_recurrence_weighted_line A b α β hα hβ e₁ e₂ he₁ he₂ hA hb

/-- Indicator of the lower quadrant used by the application fixtures. -/
@[expose] def quadrant (N : ℤ) (p : ℤ × ℤ) : ℂ :=
  if N ≤ p.1 ∧ N ≤ p.2 then 1 else 0

/-- Positive ramp above its independently chosen lower support. -/
@[expose] def ramp (N i : ℤ) : ℂ :=
  if N ≤ i then ((i - N + 1 : ℤ) : ℂ) else 0

private theorem difference_degree : (X - 1 : Polynomial ℂ).natDegree = 1 := by
  simpa using natDegree_X_sub_C (1 : ℂ)

private theorem quadrant_recurrent (N : ℤ) :
    ∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ),
      D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
      (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → quadrant N n = 0) ∧
      (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
        ∑ i ∈ Finset.range (D₁.natDegree + 1),
          ∑ l ∈ Finset.range (D₂.natDegree + 1),
            D₁.coeff i * D₂.coeff l *
              quadrant N (N₁ + (m₁ : ℤ) - (i : ℤ),
                N₁ + (m₂ : ℤ) - (l : ℤ)) = 0) := by
  refine ⟨N, X - 1, X - 1, 1, by simp, by simp, ?_, ?_⟩
  · intro n hn
    simp only [quadrant]
    rw [ite_eq_right (by omega)]
  · intro m₁ m₂ hm
    rw [difference_degree]
    norm_num [Finset.sum_range_succ, Polynomial.coeff_sub,
      Polynomial.coeff_X, Polynomial.coeff_one]
    dsimp [quadrant]
    split_ifs <;> first | omega | norm_num

private theorem ramp_recurrent (N : ℤ) :
    ∃ (N₂ : ℤ) (E : Polynomial ℂ) (M : ℕ), E.eval 0 ≠ 0 ∧
      (∀ m : ℤ, m < N₂ → ramp N m = 0) ∧
      (∀ m : ℕ, M ≤ m → ∑ i ∈ Finset.range (E.natDegree + 1),
        E.coeff i * ramp N (N₂ + (m : ℤ) - (i : ℤ)) = 0) := by
  refine ⟨N, (X - 1) ^ 2, 2, by simp, ?_, ?_⟩
  · intro m hm
    exact ite_eq_right (by omega)
  · intro m hm
    have hd : ((X - 1 : Polynomial ℂ) ^ 2).natDegree = 2 := by
      rw [natDegree_pow, difference_degree]
    have hc : (X - 1 : Polynomial ℂ) ^ 2 = X ^ 2 - C 2 * X + 1 := by
      simp only [map_ofNat]
      ring
    rw [hd]
    norm_num [Finset.sum_range_succ, hc, Polynomial.coeff_add,
      Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_one]
    simp only [ramp, show N ≤ N + (m : ℤ) by omega,
      show N ≤ N + (m : ℤ) - 1 by omega,
      show N ≤ N + (m : ℤ) - 2 by omega, ite_true]
    push_cast
    ring

/-- The explicit weighted-ramp shell used only in the importing applications. -/
@[expose] def line (N₁ N₂ : ℤ) (e₁ e₂ : ℕ) (α β : ℂ) (t : ℤ) : ℂ :=
  ∑ᶠ n : ℤ × ℤ, if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then
    quadrant N₁ n * ramp N₂ n.1 * α ^ n.1 * β ^ n.2 else 0

/-- Restricted partitions weighted by a positive ramp, for all independent
lower supports and positive weights, including common factors. -/
theorem restricted_partitions (N₁ N₂ : ℤ) (e₁ e₂ : ℕ)
    (he₁ : 0 < e₁) (he₂ : 0 < e₂) :
    ∃ (N : ℤ) (D : Polynomial ℂ) (M : ℕ), D.eval 0 ≠ 0 ∧
      (∀ m : ℤ, m < N → line N₁ N₂ e₁ e₂ 1 1 m = 0) ∧
      (∀ m : ℕ, M ≤ m → ∑ i ∈ Finset.range (D.natDegree + 1),
        D.coeff i * line N₁ N₂ e₁ e₂ 1 1 (N + (m : ℤ) - (i : ℤ)) = 0) :=
  exists_recurrence_weighted_line (quadrant N₁) (ramp N₂)
    1 1 one_ne_zero one_ne_zero e₁ e₂ he₁ he₂
    (quadrant_recurrent N₁) (ramp_recurrent N₂)

/-- A restricted-partition tail is determined by its finite canonical initial
state. Both its solution space and its initial-state equivalence come from the
recurrence supplied by the weighted-line closure. -/
theorem restricted_partition_initial_data (N₁ N₂ : ℤ) (e₁ e₂ : ℕ)
    (he₁ : 0 < e₁) (he₂ : 0 < e₂) :
    ∃ (N : ℤ) (M : ℕ) (E : LinearRecurrence ℂ),
      E.IsSolution (fun n => line N₁ N₂ e₁ e₂ 1 1 (N + (M : ℤ) + (n : ℤ))) ∧
      ∀ s : E.solSpace,
        (∀ i : Fin E.order, (s : ℕ → ℂ) i =
          line N₁ N₂ e₁ e₂ 1 1 (N + (M : ℤ) + (i : ℤ))) →
        ∀ n : ℕ, (s : ℕ → ℂ) n =
          line N₁ N₂ e₁ e₂ 1 1 (N + (M : ℤ) + (n : ℤ)) := by
  obtain ⟨N, D, M, hD, _, hrec⟩ :=
    restricted_partitions N₁ N₂ e₁ e₂ he₁ he₂
  obtain ⟨E, _, hs⟩ := exists_isSolution_tail
    (line N₁ N₂ e₁ e₂ 1 1) N D M hD hrec
  refine ⟨N, M, E, hs, ?_⟩
  intro s hi n
  let u : E.solSpace := ⟨_, (E.is_sol_iff_mem_solSpace _).mp hs⟩
  have hinit : E.toInit s = E.toInit u := funext hi
  exact congrArg (fun v : E.solSpace => (v : ℕ → ℂ) n)
    (E.toInit.injective hinit)

/-- Both unequal negative supports, with coprime and noncoprime weights. -/
theorem restricted_partition_cases
    (p : ℤ × ℤ) (hp : p ∈ ({(-1, -3), (-3, -1)} : Finset (ℤ × ℤ)))
    (w : ℕ × ℕ) (hw : w ∈ ({(2, 3), (2, 4)} : Finset (ℕ × ℕ))) :
    ∃ (N : ℤ) (D : Polynomial ℂ) (M : ℕ), D.eval 0 ≠ 0 ∧
      (∀ m : ℤ, m < N → line p.1 p.2 w.1 w.2 1 1 m = 0) ∧
      (∀ m : ℕ, M ≤ m → ∑ i ∈ Finset.range (D.natDegree + 1),
        D.coeff i * line p.1 p.2 w.1 w.2 1 1 (N + (m : ℤ) - (i : ℤ)) = 0) := by
  have hwpos : 0 < w.1 ∧ 0 < w.2 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl <;> decide
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;>
    exact restricted_partitions _ _ w.1 w.2 hwpos.1 hwpos.2

/-- Every odd shell is a genuine hole for weights `(2,4)`. -/
theorem odd_shell_zero (k : ℤ) : line 0 0 2 4 1 1 (2 * k + 1) = 0 := by
  have h (n : ℤ × ℤ) : (2 : ℤ) * n.1 + 4 * n.2 ≠ 2 * k + 1 := by omega
  simp only [line, Nat.cast_ofNat, h, ite_false, finsum_zero]

/-- The first supported shell consists of one lattice point, even when the
independent support bounds differ or are negative. -/
theorem first_shell_value (N₁ N₂ : ℤ) (e₁ e₂ : ℕ)
    (he₁ : 0 < e₁) (he₂ : 0 < e₂) (α β : ℂ) :
    line N₁ N₂ e₁ e₂ α β ((e₁ : ℤ) * max N₁ N₂ + (e₂ : ℤ) * N₁) =
      ((max N₁ N₂ - N₂ + 1 : ℤ) : ℂ) * α ^ max N₁ N₂ * β ^ N₁ := by
  have he₁' : (0 : ℤ) < e₁ := by exact_mod_cast he₁
  have he₂' : (0 : ℤ) < e₂ := by exact_mod_cast he₂
  unfold line
  rw [finsum_eq_single _ (max N₁ N₂, N₁)]
  · simp [quadrant, ramp]
  · intro n hn
    split_ifs with h
    · by_cases hq : N₁ ≤ n.1 ∧ N₁ ≤ n.2
      · by_cases hr : N₂ ≤ n.1
        · have hmax : max N₁ N₂ ≤ n.1 := max_le hq.1 hr
          have hx : n.1 = max N₁ N₂ := by nlinarith [hq.2]
          have hy : n.2 = N₁ := by nlinarith [hq.1]
          exact (hn (Prod.ext hx hy)).elim
        · simp [quadrant, ramp, hq, hr]
      · simp [quadrant, hq]
    · rfl

/-- The noncoprime example has a nonzero even shell as well as odd holes. -/
theorem even_shell_nonzero : ∃ k : ℤ, line 0 0 2 4 1 1 (2 * k) ≠ 0 := by
  refine ⟨0, ?_⟩
  have h := first_shell_value 0 0 2 4 (by decide) (by decide) 1 1
  norm_num at h ⊢
  rw [h]
  exact one_ne_zero

/-- Neither of the twisted negative-support examples is the zero sequence. -/
theorem transformed_shell_nonzero :
    line (-1) (-3) 2 3 2 3 (-5) = 1 / 2 ∧
      line (-3) (-1) 2 3 2 3 (-11) = 1 / 54 := by
  constructor
  · have h := first_shell_value (-1) (-3) 2 3 (by decide) (by decide) 2 3
    norm_num at h ⊢
    exact h
  · have h := first_shell_value (-3) (-1) 2 3 (by decide) (by decide) 2 3
    norm_num at h ⊢
    exact h

/-- The closure witnesses determine the shift `N + M`. Only after the
all-index adapter is proved do we apply the existing complex-growth theorem. -/
theorem transformed_tail_growth (N₁ N₂ : ℤ) :
    ∃ (N : ℤ) (M : ℕ) (E : LinearRecurrence ℂ) (g : ℤ),
      E.IsSolution (fun n => line N₁ N₂ 2 3 2 3 (N + (M : ℤ) + (n : ℤ))) ∧
      1 ≤ g ∧ ∀ n : ℕ,
        ‖line N₁ N₂ 2 3 2 3 (N + (M : ℤ) + (n : ℤ))‖ <
          (g : ℝ) ^ (n + 1) := by
  obtain ⟨N, D, M, hD, _, hrec⟩ :=
    exists_recurrence_weighted_line (quadrant N₁) (ramp N₂)
      2 3 (by norm_num) (by norm_num) 2 3 (by decide) (by decide)
      (quadrant_recurrent N₁) (ramp_recurrent N₂)
  obtain ⟨E, _, hE⟩ := exists_isSolution_tail
    (line N₁ N₂ 2 3 2 3) N D M hD hrec
  obtain ⟨g, hg, hbound⟩ :=
    MetaMathlibExt.exists_norm_lt_pow_of_isSolution E _ hE
  exact ⟨N, M, E, g, hE, hg, hbound⟩

/-- Both requested unequal negative support choices use the growth consumer. -/
theorem transformed_tail_cases
    (p : ℤ × ℤ) (hp : p ∈ ({(-1, -3), (-3, -1)} : Finset (ℤ × ℤ))) :
    ∃ (N : ℤ) (M : ℕ) (E : LinearRecurrence ℂ) (g : ℤ),
      E.IsSolution (fun n => line p.1 p.2 2 3 2 3 (N + (M : ℤ) + (n : ℤ))) ∧
      1 ≤ g ∧ ∀ n : ℕ,
        ‖line p.1 p.2 2 3 2 3 (N + (M : ℤ) + (n : ℤ))‖ <
          (g : ℝ) ^ (n + 1) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> exact transformed_tail_growth _ _

/-- Pointwise multiplication is not Cauchy convolution. -/
theorem fibonacci_operations_differ :
    (Nat.fib 1 : ℂ) ^ 2 ≠
      ∑ i ∈ Finset.range (1 + 1), (Nat.fib i : ℂ) * Nat.fib (1 - i) := by
  norm_num [Finset.sum_range_succ]

/-- Zero insertion is not stride sampling. -/
theorem insertion_sampling_differ :
    (if 2 ∣ 1 then (Nat.fib (1 / 2) : ℂ) else 0) ≠ (Nat.fib (2 * 1) : ℂ) := by
  norm_num

/-- A factorial sequence confined to the horizontal axis. -/
@[expose] def factorialAxis (n : ℤ × ℤ) : ℂ :=
  if n.2 = 0 ∧ 0 ≤ n.1 then (n.1.toNat.factorial : ℂ) else 0

/-- The AND-only interior hypothesis cannot enforce the required OR strips. -/
theorem factorial_interior (m₁ m₂ : ℕ) (_h₁ : 2 ≤ m₁) (h₂ : 2 ≤ m₂) :
    ∑ i ∈ Finset.range ((X - 1 : Polynomial ℂ).natDegree + 1),
      ∑ l ∈ Finset.range ((X - 1 : Polynomial ℂ).natDegree + 1),
        (X - 1 : Polynomial ℂ).coeff i * (X - 1 : Polynomial ℂ).coeff l *
          factorialAxis ((m₁ : ℤ) - (i : ℤ), (m₂ : ℤ) - (l : ℤ)) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro l hl
  have hl' : l < 2 := by simpa [difference_degree] using hl
  have hne : (m₂ : ℤ) - (l : ℤ) ≠ 0 := by omega
  simp [factorialAxis, hne]

/-- The factorial-axis residual is nonzero on a strip covered only by OR. -/
theorem factorial_strip_residual :
    ∑ i ∈ Finset.range ((X - 1 : Polynomial ℂ).natDegree + 1),
      ∑ l ∈ Finset.range ((X - 1 : Polynomial ℂ).natDegree + 1),
        (X - 1 : Polynomial ℂ).coeff i * (X - 1 : Polynomial ℂ).coeff l *
          factorialAxis (5 - (i : ℤ), -(l : ℤ)) = 96 := by
  rw [difference_degree]
  norm_num [Finset.sum_range_succ, Polynomial.coeff_sub,
    Polynomial.coeff_X, Polynomial.coeff_one, factorialAxis, Nat.factorial]

/-- With a zero weight, even a lower-quadrant fiber is infinite. This limits
the finite-fiber proof method; it is not a nonrecurrence assertion. -/
theorem zero_weight_infinite_fiber :
    Set.Infinite {n : ℤ × ℤ | 0 ≤ n.1 ∧ 0 ≤ n.2 ∧
      (0 : ℤ) * n.1 + (1 : ℤ) * n.2 = 0} := by
  have hinj : Function.Injective (fun k : ℕ => ((k : ℤ), (0 : ℤ))) := by
    intro a b h
    have h' : (a : ℤ) = (b : ℤ) := congrArg Prod.fst h
    exact_mod_cast h'
  apply (Set.infinite_range_of_injective hinj).mono
  rintro n ⟨k, rfl⟩
  simp

/-- A nonzero constant denominator gives order zero on the translated tail,
without asserting that the earlier finitely supported sequence vanishes. -/
theorem order_zero_tail :
    ∃ E : LinearRecurrence ℂ, E.order = 0 ∧
      E.IsSolution (fun n : ℕ => if (-3 : ℤ) + 2 + n = -2 then (1 : ℂ) else 0) ∧
      ∀ n : ℕ, (if (-3 : ℤ) + 2 + n = -2 then (1 : ℂ) else 0) = 0 := by
  let x : ℤ → ℂ := fun z => if z = -2 then 1 else 0
  have hr : ∀ m : ℕ, 2 ≤ m →
      ∑ i ∈ Finset.range ((1 : Polynomial ℂ).natDegree + 1),
      (1 : Polynomial ℂ).coeff i * x (-3 + (m : ℤ) - (i : ℤ)) = 0 := by
    intro m hm
    have hne : (-3 : ℤ) + m ≠ -2 := by omega
    simp [x, hne]
  obtain ⟨E, ho, hs⟩ := exists_isSolution_tail x (-3) 1 2 (by simp) hr
  have horder : E.order = 0 := by simpa using ho
  refine ⟨E, horder, hs, ?_⟩
  intro n
  have h := hs n
  simpa [horder, x] using h

/-- Canonical state transition agrees with shifting an all-index solution. -/
theorem canonical_shift_state (E : LinearRecurrence ℂ) (s : ℕ → ℂ)
    (hs : E.IsSolution s) (i : Fin E.order) :
    E.tupleSucc (fun j => s j) i = s (i + 1) := by
  simp only [LinearRecurrence.tupleSucc, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs with hi
  · rfl
  · have heq : (i : ℕ) + 1 = E.order := by omega
    rw [heq]
    simpa using (hs 0).symm

end WeightedLineTest

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MonotoneJuntaApproximationAMR127Problem0022

@[expose] public section

namespace MathlibExt.Combinatorics.MonotoneJuntaApproximationAMR127Problem0022Wanted

example : ¬ servedioTanVerbinConjecture := servedioTanVerbinConjecture_refuted

/-- The refutation, unfolded: one `ε > 0` defeats every polynomial junta size `(deg f + 2) ^ C`,
with a monotone function that differs from every such junta on more than `ε 2ⁿ` inputs. -/
example : ∃ ε : ℝ, 0 < ε ∧ ∀ C : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool), Monotone f ∧
    ∀ (J : Finset (Fin n)) (g : (Fin n → Bool) → Bool),
      J.card ≤ (BooleanCube.booleanDegree f + 2) ^ C → DependsOn g (J : Set (Fin n)) →
        ε * 2 ^ n < ((Finset.univ.filter fun x => f x ≠ g x).card : ℝ) := by
  have h := servedioTanVerbinConjecture_refuted
  simp only [servedioTanVerbinConjecture, not_forall, not_exists, not_and, not_le] at h
  obtain ⟨ε, hε, h⟩ := h
  refine ⟨ε, hε, fun C => ?_⟩
  obtain ⟨n, f, hf, h⟩ := h C
  exact ⟨n, f, hf, fun J g hJ hg => h J g hJ hg⟩

/-- In a fixed dimension `n` the conclusion of the conjecture holds with `C = n` for every
function, even with `g = f`: all `n` coordinates fit, since `n ≤ 2 ^ n ≤ (deg f + 2) ^ n`. A
counterexample must therefore use unboundedly many coordinates. -/
example (ε : ℝ) (hε : 0 < ε) (n : ℕ) (f : (Fin n → Bool) → Bool) :
    ∃ (J : Finset (Fin n)) (g : (Fin n → Bool) → Bool),
      J.card ≤ (BooleanCube.booleanDegree f + 2) ^ n ∧ DependsOn g (J : Set (Fin n)) ∧
        ((Finset.univ.filter fun x => f x ≠ g x).card : ℝ) ≤ ε * 2 ^ n := by
  refine ⟨Finset.univ, f, ?_, ?_, ?_⟩
  · rw [Finset.card_univ, Fintype.card_fin]
    calc n ≤ 2 ^ n := Nat.lt_two_pow_self.le
      _ ≤ (BooleanCube.booleanDegree f + 2) ^ n := Nat.pow_le_pow_left (by omega) n
  · intro x y hxy
    congr 1
    funext i
    exact hxy i (by simp)
  · simp only [ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hε.le (pow_nonneg zero_le_two n)

/-- A coordinate projection (dictator) is monotone, has Boolean degree one, and is a junta on
its own coordinate, so it satisfies the conclusion of the conjecture with `C = 0`. -/
example (ε : ℝ) (hε : 0 < ε) (n : ℕ) (i : Fin n) :
    Monotone (fun x : Fin n → Bool => x i) ∧
      ∃ (J : Finset (Fin n)) (g : (Fin n → Bool) → Bool),
        J.card ≤ (BooleanCube.booleanDegree (fun x : Fin n → Bool => x i) + 2) ^ 0 ∧
          DependsOn g (J : Set (Fin n)) ∧
          ((Finset.univ.filter fun x : Fin n → Bool => x i ≠ g x).card : ℝ) ≤ ε * 2 ^ n := by
  refine ⟨fun x y hxy => hxy i, {i}, fun x => x i, by simp, ?_, ?_⟩
  · intro x y hxy
    exact hxy i (by simp)
  · simp only [ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hε.le (pow_nonneg zero_le_two n)

end MathlibExt.Combinatorics.MonotoneJuntaApproximationAMR127Problem0022Wanted

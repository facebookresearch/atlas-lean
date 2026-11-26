/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.RateMatrix
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.Ring

/-!
# Finite active-population generator

The birth-death generator on finitely many active states has nonnegative off-diagonal entries and closed endpoints.
-/

@[expose] public section

open Finset Matrix

namespace MathlibExt.Biology.Dynamics.FiniteActivePopulation.Generator

/-- The birth-death generator on states `Fin (N + 1)`: births at
rate `b i = (N - i) * f i`, deaths at rate `d i = alpha * i`, with
the negative row sum on the diagonal and zero elsewhere. -/
noncomputable def birthDeathGenerator (N : ℕ) (alpha : ℝ) (f : ℕ → ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i j =>
    if (j : ℕ) = (i : ℕ) + 1 then ((N : ℝ) - i) * f i
    else if (j : ℕ) + 1 = i then alpha * (i : ℝ)
    else if j = i then -(((N : ℝ) - i) * f i + alpha * (i : ℝ))
    else 0

/-- **Off-diagonal entries are nonnegative.** For `alpha ≥ 0`,
`f i ≥ 0`, and states `i ≤ N`, every off-diagonal entry of the
birth-death generator is nonnegative. -/
theorem birthDeath_offDiag_nonneg (N : ℕ) (alpha : ℝ) (f : ℕ → ℝ)
    (halpha : 0 ≤ alpha) (hf : ∀ i : Fin (N + 1), 0 ≤ f (i : ℕ))
    {i j : Fin (N + 1)} (hij : i ≠ j) :
    0 ≤ birthDeathGenerator N alpha f i j := by
  unfold birthDeathGenerator
  by_cases h1 : (j : ℕ) = (i : ℕ) + 1
  · simp only [h1, ite_true]
    apply mul_nonneg _ (hf _)
    exact sub_nonneg.mpr (Nat.cast_le.mpr (Fin.is_le i))
  · simp only [h1, ite_false]
    by_cases h2 : (j : ℕ) + 1 = i
    · simp only [h2, ite_true]
      apply mul_nonneg halpha
      exact Nat.cast_nonneg _
    · simp only [h2, ite_false]
      have h3 : ¬(j = i) := fun h => hij h.symm
      simp only [h3, ite_false, le_refl]

/-- **Endpoints close the population.** There is no death from
state `0` and no birth from state `N`: the would-be outward rates
vanish at the endpoints. -/
theorem birthDeath_endpoints (N : ℕ) (alpha : ℝ) (f : ℕ → ℝ) :
    alpha * (0 : ℝ) = 0 ∧ ((N : ℝ) - N) * f N = 0 := by
  exact ⟨mul_zero alpha, by rw [sub_self, zero_mul]⟩


private lemma birthDeath_birth_sum (N : ℕ) (f : ℕ → ℝ) (i : Fin (N + 1)) :
    ∑ j : Fin (N + 1), (if (j : ℕ) = (i : ℕ) + 1 then (((N : ℝ) - i) * f i : ℝ) else 0)
      = (((N : ℝ) - i) * f i : ℝ) := by
  have huniq : ∀ j1 j2 : Fin (N + 1), (j1 : ℕ) = (i : ℕ) + 1 → (j2 : ℕ) = (i : ℕ) + 1 → j1 = j2 := by
    intro j1 j2 h1 h2
    have hval : (j1 : ℕ) = (j2 : ℕ) := by rw [h1, h2]
    exact Fin.ext hval
  have hsum := Fintype.sum_ite_eq_ite_exists (fun j : Fin (N + 1) => (j : ℕ) = (i : ℕ) + 1) huniq ((((N : ℝ) - i) * f i : ℝ))
  rw [hsum]
  by_cases hex : ∃ j : Fin (N + 1), (j : ℕ) = (i : ℕ) + 1
  · simp [hex]
  · simp only [hex, ite_false]
    have hi_le : (i : ℕ) ≤ N := Nat.le_of_lt_succ i.2
    have hi_eq : (i : ℕ) = N := by
      by_contra hne
      have hlt : (i : ℕ) < N := Nat.lt_of_le_of_ne hi_le hne
      have h1lt : (i : ℕ) + 1 < N + 1 := Nat.succ_lt_succ hlt
      exact hex ⟨⟨(i : ℕ) + 1, h1lt⟩, rfl⟩
    have hcast : ((i : Fin (N + 1)) : ℝ) = (N : ℝ) := by
      have h1 : ((i : ℕ) : ℝ) = (N : ℝ) := by rw [hi_eq]
      exact h1
    rw [hcast]
    ring

private lemma birthDeath_death_sum (N : ℕ) (alpha : ℝ) (i : Fin (N + 1)) :
    ∑ j : Fin (N + 1), (if (j : ℕ) + 1 = (i : ℕ) then (alpha * (i : ℝ) : ℝ) else 0)
      = (alpha * (i : ℝ) : ℝ) := by
  have huniq : ∀ j1 j2 : Fin (N + 1), (j1 : ℕ) + 1 = (i : ℕ) → (j2 : ℕ) + 1 = (i : ℕ) → j1 = j2 := by
    intro j1 j2 h1 h2
    have heq : (j1 : ℕ) + 1 = (j2 : ℕ) + 1 := h1.trans h2.symm
    have hval : (j1 : ℕ) = (j2 : ℕ) := Nat.add_right_cancel heq
    exact Fin.ext hval
  have hsum := Fintype.sum_ite_eq_ite_exists (fun j : Fin (N + 1) => (j : ℕ) + 1 = (i : ℕ)) huniq ((alpha * (i : ℝ) : ℝ))
  rw [hsum]
  by_cases hex : ∃ j : Fin (N + 1), (j : ℕ) + 1 = (i : ℕ)
  · simp [hex]
  · simp only [hex, ite_false]
    have hi_eq : (i : ℕ) = 0 := by
      by_contra hne
      have hpos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hne
      have hmem : (i : ℕ) - 1 < N + 1 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.2
      have hwit : ((⟨(i : ℕ) - 1, hmem⟩ : Fin (N + 1)) : ℕ) + 1 = (i : ℕ) := Nat.sub_add_cancel hpos
      exact hex ⟨⟨(i : ℕ) - 1, hmem⟩, hwit⟩
    have hcast : ((i : Fin (N + 1)) : ℝ) = 0 := by
      have h1 : ((i : ℕ) : ℝ) = 0 := by rw [hi_eq]; simp
      exact h1
    rw [hcast]
    ring

theorem birthDeath_decomp (N : ℕ) (alpha : ℝ) (f : ℕ → ℝ) (i j : Fin (N + 1)) :
    birthDeathGenerator N alpha f i j =
      (if (j : ℕ) = (i : ℕ) + 1 then (((N : ℝ) - i) * f i : ℝ) else 0) +
      (if (j : ℕ) + 1 = (i : ℕ) then (alpha * (i : ℝ) : ℝ) else 0) +
      (if j = i then (-((((N : ℝ) - i) * f i : ℝ) + alpha * (i : ℝ)) : ℝ) else 0) := by
  unfold birthDeathGenerator
  by_cases h1 : (j : ℕ) = (i : ℕ) + 1
  · rw [ite_eq_left h1, ite_eq_left h1]
    have h2 : ¬ ((j : ℕ) + 1 = (i : ℕ)) := by omega
    have h3 : ¬ (j = i) := by
      intro hcon
      have hval : (j : ℕ) = (i : ℕ) := congrArg Fin.val hcon
      omega
    rw [ite_eq_right h2, ite_eq_right h3]
    ring
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : (j : ℕ) + 1 = (i : ℕ)
    · rw [ite_eq_left h2, ite_eq_left h2]
      have h3 : ¬ (j = i) := by
        intro hcon
        have hval : (j : ℕ) = (i : ℕ) := congrArg Fin.val hcon
        omega
      rw [ite_eq_right h3]
      ring
    · rw [ite_eq_right h2, ite_eq_right h2]
      ring

/-- **The birth-death generator is a rate matrix.** For
`alpha ≥ 0` and `f i ≥ 0`, the birth-death generator satisfies
`ProbabilityTheory.IsRateMatrix`: off-diagonal entries are
nonnegative and every row sums to zero. -/
theorem birthDeath_isRateMatrix (N : ℕ) (alpha : ℝ) (f : ℕ → ℝ)
    (halpha : 0 ≤ alpha) (hf : ∀ i : Fin (N + 1), 0 ≤ f (i : ℕ)) :
    ProbabilityTheory.IsRateMatrix (birthDeathGenerator N alpha f) := by
  constructor
  · intro i j hij
    unfold birthDeathGenerator
    by_cases h1 : (j : ℕ) = (i : ℕ) + 1
    · simp [h1]
      apply mul_nonneg
      · have hi : (i : ℕ) ≤ N := Nat.le_of_lt_succ i.2
        have hcast : ((i : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hi
        exact sub_nonneg.mpr hcast
      · exact hf _
    · simp [h1]
      by_cases h2 : (j : ℕ) + 1 = (i : ℕ)
      · simp [h2]
        exact mul_nonneg halpha (Nat.cast_nonneg _)
      · simp [h2]
        by_cases h3 : j = i
        · subst h3
          exact absurd rfl hij
        · simp [h3]
  · intro i
    have hpoint : ∀ j : Fin (N + 1), birthDeathGenerator N alpha f i j =
        (if (j : ℕ) = (i : ℕ) + 1 then (((N : ℝ) - i) * f i : ℝ) else 0) +
        (if (j : ℕ) + 1 = (i : ℕ) then (alpha * (i : ℝ) : ℝ) else 0) +
        (if j = i then (-((((N : ℝ) - i) * f i : ℝ) + alpha * (i : ℝ)) : ℝ) else 0) :=
      fun j => birthDeath_decomp N alpha f i j
    have hsum : ∑ j : Fin (N + 1), birthDeathGenerator N alpha f i j =
        ∑ j : Fin (N + 1), ((if (j : ℕ) = (i : ℕ) + 1 then (((N : ℝ) - i) * f i : ℝ) else 0) +
        (if (j : ℕ) + 1 = (i : ℕ) then (alpha * (i : ℝ) : ℝ) else 0) +
        (if j = i then (-((((N : ℝ) - i) * f i : ℝ) + alpha * (i : ℝ)) : ℝ) else 0)) :=
      Finset.sum_congr rfl (fun j _ => hpoint j)
    rw [hsum, Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [birthDeath_birth_sum N f i, birthDeath_death_sum N alpha i]
    simp

/-- **Endpoint diagonal entries.** The diagonal at state `0` is
`-(N * f 0)` (births only), and the diagonal at the top state
`N` is `-(alpha * N)` (deaths only). -/
theorem birthDeath_endpoint_diag (N : ℕ) (alpha : ℝ) (f : ℕ → ℝ) :
    birthDeathGenerator N alpha f 0 0 = -((N : ℝ) * f 0) ∧
    birthDeathGenerator N alpha f ⟨N, Nat.lt_succ_self N⟩ ⟨N, Nat.lt_succ_self N⟩ =
      -(alpha * (N : ℝ)) := by
  constructor
  · simp [birthDeathGenerator]
  · simp [birthDeathGenerator]

#print axioms birthDeath_isRateMatrix
#print axioms birthDeath_endpoint_diag
#print axioms birthDeath_birth_sum
#print axioms birthDeath_death_sum
#print axioms birthDeath_decomp

end MathlibExt.Biology.Dynamics.FiniteActivePopulation.Generator

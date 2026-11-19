/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.NeymanPearsonExactSize

/-!
# Tests for the finite exact-size Neyman–Pearson test
-/

@[expose] public section

open MeasureTheory MathlibExt.Probability.Statistics.NeymanPearson

namespace MathlibExtTest.Probability.Statistics.NeymanPearsonExactSize

/-- Fixture A (atom forces randomization): with `p` uniform on `Bool`, no deterministic test
has size `1/4`. -/
example : ∀ φ : Bool → Set.Icc (0 : ℝ) 1, (∀ x, (φ x).val = 0 ∨ (φ x).val = 1) →
    ∑ x, (φ x).val * (1 / 2 : ℝ) ≠ 1 / 4 := by
  intro φ hφ
  rw [Fintype.sum_bool]
  rcases hφ true with h1 | h1 <;> rcases hφ false with h2 | h2 <;> rw [h1, h2] <;> norm_num

/-- Fixture A through the main theorem: the exact-size most powerful test for
`p = (1/2, 1/2)`, `q = (1/4, 3/4)`, `α = 1/4` exists and takes a strictly fractional value. -/
example : ∃ φstar : Bool → Set.Icc (0 : ℝ) 1,
    ∑ x, (φstar x).val * (1 / 2 : ℝ) = 1 / 4 ∧
    (∀ φ : Bool → Set.Icc (0 : ℝ) 1, ∑ x, (φ x).val * (1 / 2 : ℝ) ≤ 1 / 4 →
      ∑ x, (φ x).val * (if x then (3 / 4 : ℝ) else 1 / 4) ≤
        ∑ x, (φstar x).val * (if x then (3 / 4 : ℝ) else 1 / 4)) ∧
    ∃ x, 0 < (φstar x).val ∧ (φstar x).val < 1 := by
  obtain ⟨_, -, _, -, φstar, -, -, -, hsize, hopt⟩ :=
    exists_exact_size_most_powerful_finite (fun _ : Bool => (1 / 2 : ℝ))
      (fun x : Bool => if x then (3 / 4 : ℝ) else 1 / 4)
      (fun _ => by norm_num) (fun x => by cases x <;> norm_num)
      (by rw [Fintype.sum_bool]; norm_num) (by rw [Fintype.sum_bool]; norm_num)
      (1 / 4) (by norm_num) (by norm_num)
  refine ⟨φstar, hsize, hopt, ?_⟩
  by_contra hcon
  have hdet : ∀ x, (φstar x).val = 0 ∨ (φstar x).val = 1 := fun x =>
    (φstar x).2.1.eq_or_lt.elim (fun h => Or.inl h.symm)
      (fun h => Or.inr (le_antisymm (φstar x).2.2 (not_lt.mp fun h' => hcon ⟨x, h, h'⟩)))
  rw [Fintype.sum_bool] at hsize
  rcases hdet true with h1 | h1 <;> rcases hdet false with h2 | h2 <;>
    rw [h1, h2] at hsize <;> norm_num at hsize

/-- Fixture B (zero null mass): a point with `p x = 0 < q x` is rejected by every test
satisfying the rejection clause, for every threshold `k ≥ 0`. -/
example (k : ℝ) (hk : 0 ≤ k) (φstar : Fin 3 → Set.Icc (0 : ℝ) 1)
    (hgt : ∀ x, k * (![1 / 2, 1 / 2, 0] : Fin 3 → ℝ) x < (![0, 1 / 2, 1 / 2] : Fin 3 → ℝ) x →
      (φstar x).val = 1) :
    (φstar 2).val = 1 := by
  have hp2 : (![1 / 2, 1 / 2, 0] : Fin 3 → ℝ) 2 = 0 := by simp
  have hq2 : (![0, 1 / 2, 1 / 2] : Fin 3 → ℝ) 2 = 1 / 2 := by simp
  exact hgt 2 ((mul_nonpos_of_nonneg_of_nonpos hk hp2.le).trans_lt (by rw [hq2]; norm_num))

/-- Fixture B through the main theorem at `α = 1/4`: the zero-null-mass point is rejected at
no size cost and the power is at least its alternative mass `1/2`. -/
example : ∃ φstar : Fin 3 → Set.Icc (0 : ℝ) 1,
    ∑ x, (φstar x).val * (![1 / 2, 1 / 2, 0] : Fin 3 → ℝ) x = 1 / 4 ∧
    (φstar 2).val = 1 ∧
    1 / 2 ≤ ∑ x, (φstar x).val * (![0, 1 / 2, 1 / 2] : Fin 3 → ℝ) x := by
  obtain ⟨_, -, _, -, φstar, hgt, -, -, hsize, -⟩ :=
    exists_exact_size_most_powerful_finite (![1 / 2, 1 / 2, 0] : Fin 3 → ℝ)
      (![0, 1 / 2, 1 / 2] : Fin 3 → ℝ)
      (fun x => by fin_cases x <;> norm_num) (fun x => by fin_cases x <;> norm_num)
      (by rw [Fin.sum_univ_three]; norm_num) (by rw [Fin.sum_univ_three]; norm_num)
      (1 / 4) (by norm_num) (by norm_num)
  have h2 : (φstar 2).val = 1 := hgt 2 (by norm_num)
  refine ⟨φstar, hsize, h2, ?_⟩
  have hpow : ∑ x, (φstar x).val * (![0, 1 / 2, 1 / 2] : Fin 3 → ℝ) x =
      (φstar 1).val * (1 / 2) + 1 / 2 := by
    rw [Fin.sum_univ_three, h2]
    norm_num
  rw [hpow]
  linarith [mul_nonneg (φstar 1).2.1 (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- Fixture C (all likelihood ratios tied, `p = q` uniform on `Bool`, `α = 1/3`): the clauses
of the main theorem force the threshold onto the tie, `k = 1`, and the tie value `γ = α`. -/
example (k γ : ℝ) (hk : 0 ≤ k) (φstar : Bool → Set.Icc (0 : ℝ) 1)
    (hgt : ∀ x : Bool, k * (1 / 2 : ℝ) < 1 / 2 → (φstar x).val = 1)
    (hlt : ∀ x : Bool, (1 / 2 : ℝ) < k * (1 / 2) → (φstar x).val = 0)
    (heq : ∀ x : Bool, (1 / 2 : ℝ) = k * (1 / 2) → (φstar x).val = γ)
    (hsize : ∑ x, (φstar x).val * (1 / 2 : ℝ) = 1 / 3) :
    k = 1 ∧ γ = 1 / 3 := by
  rw [Fintype.sum_bool] at hsize
  rcases lt_trichotomy k 1 with h | rfl | h
  · have h' : k * (1 / 2 : ℝ) < 1 / 2 := by linarith
    rw [hgt true h', hgt false h'] at hsize
    norm_num at hsize
  · have h' : (1 / 2 : ℝ) = 1 * (1 / 2) := by norm_num
    rw [heq true h', heq false h'] at hsize
    exact ⟨rfl, by linarith⟩
  · have h' : (1 / 2 : ℝ) < k * (1 / 2) := by linarith
    rw [hlt true h', hlt false h'] at hsize
    norm_num at hsize

end MathlibExtTest.Probability.Statistics.NeymanPearsonExactSize

#print axioms MathlibExt.Probability.Statistics.NeymanPearson.exists_exact_size_most_powerful_finite

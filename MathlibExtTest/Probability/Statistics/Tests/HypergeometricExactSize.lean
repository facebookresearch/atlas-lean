/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Tests.HypergeometricExactSize

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Tests.HypergeometricExactSize

open ProbabilityTheory

/-- Fixture A (use): the single-free-cell 2×2 table has closed-form masses `1/2, 1/2`. -/
example : hypergeometricReal 2 1 1 0 = 1 / 2 ∧ hypergeometricReal 2 1 1 1 = 1 / 2 := by
  have h1 : (2 : ℕ) - 1 = 1 := rfl
  have h3 : (1 : ℕ) - 1 = 0 := rfl
  have c10 : Nat.choose 1 0 = 1 := rfl
  have c11 : Nat.choose 1 1 = 1 := rfl
  have c21 : Nat.choose 2 1 = 2 := rfl
  unfold hypergeometricReal
  simp only [ite_eq_left (show (0 : ℕ) ≤ 1 from by decide),
    ite_eq_left (show (1 : ℕ) ≤ 1 from by decide), h1, h3, c10, c11, c21]
  norm_num

/-- Fixture B (use, through the normalization API): the hypergeometric masses normalize
over the support. -/
example (N K m : ℕ) (hK : K ≤ N) (hm : m ≤ N) :
    ∑ j : Fin (m + 1), hypergeometricReal N K m (j.val : ℕ) = 1 := by
  have h := sum_hypergeometricReal (N := N) (K := K) (n := m) hK hm
  rw [Fin.sum_univ_eq_sum_range]
  exact h

/-- Fixture C (boundary `m = 0`, through the main theorem): with no draws the support is the
single count `0`, where both laws put mass `1`. For every population size, pair of margins and
level `α`, the returned most powerful test is the constant `α`, so its power is `α`. -/
example (N K₀ K₁ : ℕ) (hK₀ : K₀ ≤ N) (hK₁ : K₁ ≤ N) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ φstar : Fin 1 → Set.Icc (0 : ℝ) 1,
      ∑ j, (φstar j).val * hypergeometricReal N K₀ 0 (j.val : ℕ) = α ∧
      (∀ φ : Fin 1 → Set.Icc (0 : ℝ) 1,
        ∑ j, (φ j).val * hypergeometricReal N K₀ 0 (j.val : ℕ) ≤ α →
          ∑ j, (φ j).val * hypergeometricReal N K₁ 0 (j.val : ℕ) ≤
            ∑ j, (φstar j).val * hypergeometricReal N K₁ 0 (j.val : ℕ)) ∧
      (φstar 0).val = α ∧
      ∑ j, (φstar j).val * hypergeometricReal N K₁ 0 (j.val : ℕ) = α := by
  obtain ⟨_, -, _, -, φstar, -, -, -, hsize, hopt⟩ :=
    MathlibExt.Probability.Statistics.Tests.hypergeometric_exact_size_most_powerful
      N K₀ K₁ 0 hK₀ hK₁ (Nat.zero_le N) α hα0 hα1
  have hsum : ∀ K, ∑ j : Fin 1, (φstar j).val * hypergeometricReal N K 0 (j.val : ℕ) =
      (φstar 0).val := fun K => by
    simp [hypergeometricReal]
  have h0 : (φstar 0).val = α := (hsum K₀).symm.trans hsize
  exact ⟨φstar, hsize, hopt, h0, (hsum K₁).trans h0⟩

/-- Fixture D (interior `0 < m < N`, through the main theorem): `N = 4`, `m = 2`, null `K₀ = 1`
with masses `(1/2, 1/2, 0)`, alternative `K₁ = 3` with masses `(0, 1/2, 1/2)`, level `1/4`. The
rejection clause rejects the count `2`, which has null mass `0`; the exact size and optimality
against the size-`1/4` test `(0, 1/2, 1)` then pin the returned test to `(0, 1/2, 1)`, with
power exactly `3/4`. -/
example : ∃ φstar : Fin 3 → Set.Icc (0 : ℝ) 1,
    ∑ j, (φstar j).val * hypergeometricReal 4 1 2 (j.val : ℕ) = 1 / 4 ∧
    (∀ φ : Fin 3 → Set.Icc (0 : ℝ) 1,
      ∑ j, (φ j).val * hypergeometricReal 4 1 2 (j.val : ℕ) ≤ 1 / 4 →
        ∑ j, (φ j).val * hypergeometricReal 4 3 2 (j.val : ℕ) ≤
          ∑ j, (φstar j).val * hypergeometricReal 4 3 2 (j.val : ℕ)) ∧
    (φstar 0).val = 0 ∧ (φstar 1).val = 1 / 2 ∧ (φstar 2).val = 1 ∧
    ∑ j, (φstar j).val * hypergeometricReal 4 3 2 (j.val : ℕ) = 3 / 4 := by
  obtain ⟨k, -, _, -, φstar, hgt, -, -, hsize, hopt⟩ :=
    MathlibExt.Probability.Statistics.Tests.hypergeometric_exact_size_most_powerful
      4 1 3 2 (by norm_num) (by norm_num) (by norm_num) (1 / 4) (by norm_num) (by norm_num)
  have e0 : ((0 : Fin 3).val : ℕ) = 0 := rfl
  have e1 : ((1 : Fin 3).val : ℕ) = 1 := rfl
  have e2 : ((2 : Fin 3).val : ℕ) = 2 := rfl
  have hp : ∀ φ : Fin 3 → Set.Icc (0 : ℝ) 1,
      ∑ j, (φ j).val * hypergeometricReal 4 1 2 (j.val : ℕ) =
        (φ 0).val * (1 / 2) + (φ 1).val * (1 / 2) := by
    intro φ
    rw [Fin.sum_univ_three, e0, e1, e2]
    norm_num [hypergeometricReal, Nat.choose]
  have hq : ∀ φ : Fin 3 → Set.Icc (0 : ℝ) 1,
      ∑ j, (φ j).val * hypergeometricReal 4 3 2 (j.val : ℕ) =
        (φ 1).val * (1 / 2) + (φ 2).val * (1 / 2) := by
    intro φ
    rw [Fin.sum_univ_three, e0, e1, e2]
    norm_num [hypergeometricReal, Nat.choose]
  have h2 : (φstar (2 : Fin 3)).val = 1 :=
    hgt 2 (show k * hypergeometricReal 4 1 2 2 < hypergeometricReal 4 3 2 2 by
      norm_num [hypergeometricReal, Nat.choose])
  have hsize' := (hp φstar).symm.trans hsize
  let ψ : Fin 3 → Set.Icc (0 : ℝ) 1 :=
    ![⟨0, Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩⟩,
      ⟨1 / 2, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩,
      ⟨1, Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩⟩]
  have hψ0 : (ψ 0).val = 0 := rfl
  have hψ1 : (ψ 1).val = 1 / 2 := rfl
  have hψ2 : (ψ 2).val = 1 := rfl
  have hψsize : ∑ j, (ψ j).val * hypergeometricReal 4 1 2 (j.val : ℕ) ≤ 1 / 4 := by
    rw [hp, hψ0, hψ1]
    norm_num
  have hpow := (hq ψ).symm.trans_le ((hopt ψ hψsize).trans_eq (hq φstar))
  rw [hψ1, hψ2] at hpow
  have h0lo : 0 ≤ (φstar (0 : Fin 3)).val := (φstar 0).2.1
  refine ⟨φstar, hsize, hopt, by linarith, by linarith, h2, ?_⟩
  rw [hq φstar]
  linarith

/-- Fixture E (boundary `m = N`, through the main theorem): drawing the whole urn of `N = 2`
items makes both laws point masses at their margins, `(0, 1, 0)` for `K₀ = 1` and `(0, 0, 1)`
for `K₁ = 2`. For every level `α`, the returned test randomizes the count `1` with
probability `α` and rejects the count `2`, so its power is `1`. -/
example (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ φstar : Fin 3 → Set.Icc (0 : ℝ) 1,
      ∑ j, (φstar j).val * hypergeometricReal 2 1 2 (j.val : ℕ) = α ∧
      (∀ φ : Fin 3 → Set.Icc (0 : ℝ) 1,
        ∑ j, (φ j).val * hypergeometricReal 2 1 2 (j.val : ℕ) ≤ α →
          ∑ j, (φ j).val * hypergeometricReal 2 2 2 (j.val : ℕ) ≤
            ∑ j, (φstar j).val * hypergeometricReal 2 2 2 (j.val : ℕ)) ∧
      (φstar 1).val = α ∧ (φstar 2).val = 1 ∧
      ∑ j, (φstar j).val * hypergeometricReal 2 2 2 (j.val : ℕ) = 1 := by
  obtain ⟨k, -, _, -, φstar, hgt, -, -, hsize, hopt⟩ :=
    MathlibExt.Probability.Statistics.Tests.hypergeometric_exact_size_most_powerful
      2 1 2 2 (by norm_num) le_rfl le_rfl α hα0 hα1
  have e0 : ((0 : Fin 3).val : ℕ) = 0 := rfl
  have e1 : ((1 : Fin 3).val : ℕ) = 1 := rfl
  have e2 : ((2 : Fin 3).val : ℕ) = 2 := rfl
  have hp : ∀ φ : Fin 3 → Set.Icc (0 : ℝ) 1,
      ∑ j, (φ j).val * hypergeometricReal 2 1 2 (j.val : ℕ) = (φ 1).val := by
    intro φ
    rw [Fin.sum_univ_three, e0, e1, e2]
    norm_num [hypergeometricReal, Nat.choose]
  have hq : ∀ φ : Fin 3 → Set.Icc (0 : ℝ) 1,
      ∑ j, (φ j).val * hypergeometricReal 2 2 2 (j.val : ℕ) = (φ 2).val := by
    intro φ
    rw [Fin.sum_univ_three, e0, e1, e2]
    norm_num [hypergeometricReal, Nat.choose]
  have h2 : (φstar (2 : Fin 3)).val = 1 :=
    hgt 2 (show k * hypergeometricReal 2 1 2 2 < hypergeometricReal 2 2 2 2 by
      norm_num [hypergeometricReal, Nat.choose])
  exact ⟨φstar, hsize, hopt, (hp φstar).symm.trans hsize, h2, (hq φstar).trans h2⟩

end MathlibExtTest.Probability.Statistics.Tests.HypergeometricExactSize

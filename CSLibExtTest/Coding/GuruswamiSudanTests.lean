/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.GuruswamiSudan

/-! # Tests for the Guruswami–Sudan root-finding lemma

The bivariate polynomial `Q = Y - X` over `ℚ` has `(1, 1)`-weighted degree `1` and a simple root
at every point `(a, a)`; the root-finding lemma recovers `P = X` from two agreeing points.
-/

namespace Cslib.CodingTheory.GuruswamiSudanTests

open Polynomial Cslib.CodingTheory GuruswamiSudan

/-- `Q(X, Y) = Y - X`. -/
noncomputable def Q : ℚ[X][X] := X - C X

theorem Q_coeff_zero : Q.coeff 0 = -X := by simp [Q, coeff_X]

theorem Q_coeff_one : Q.coeff 1 = 1 := by simp [Q, coeff_X]

theorem Q_coeff_add_two (j : ℕ) : Q.coeff (j + 2) = 0 := by
  simp [Q, coeff_X]

theorem Q_weightedDegLE : WeightedDegLE 1 1 Q := by
  intro j i hij
  rcases j with _ | _ | j
  · rw [Q_coeff_zero, coeff_neg, coeff_X] at hij
    by_cases hi : i = 1
    · omega
    · exact absurd (by simp [Ne.symm hi]) hij
  · rw [Q_coeff_one, coeff_one] at hij
    by_cases hi : i = 0
    · omega
    · exact absurd (by simp [hi]) hij
  · rw [Q_coeff_add_two, coeff_zero] at hij
    exact absurd rfl hij

theorem Q_hasRootMult (a : ℚ) : HasRootMult Q a a 1 := by
  unfold HasRootMult
  rw [show pointIdeal a a ^ 1 = pointIdeal a a from pow_one _, pointIdeal]
  have h : Q = (X - C (C a)) - C (X - C a) := by simp only [Q, map_sub]; ring
  rw [h]
  exact Ideal.sub_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))

/-- The points `0, 1`. -/
def α : Fin 2 → ℚ := ![0, 1]

theorem α_injective : Function.Injective α := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [α]

-- `P = X` agrees with `y = α` at both points and `2 · 1 > 1`, so `Q(X, X) = 0`.
example : Q.eval (X : ℚ[X]) = 0 :=
  eval_eq_zero_of_agree (y := α) α_injective Q_weightedDegLE (fun i => Q_hasRootMult (α i))
    (by simp) (by simp [α])

-- Hence `Y - X` divides `Q`.
example : X - C (X : ℚ[X]) ∣ Q :=
  X_sub_C_dvd_of_agree (y := α) α_injective Q_weightedDegLE (fun i => Q_hasRootMult (α i))
    (by simp) (by simp [α])

-- Substitution respects the weighted degree.
example : (Q.eval (X + 1 : ℚ[X])).natDegree ≤ 1 :=
  natDegree_eval_le Q_weightedDegLE (by compute_degree!)

-- Reed–Solomon list size up to the Johnson radius: `n = 2`, `k = 1`, `t = 1`, `2 · 0 < 1`.
example (Ps : Finset ℚ[X]) (hPs : ∀ p ∈ Ps, p.degree < 1 ∧ 1 ≤ (Finset.univ.filter
    fun i => p.eval (α i) = α i).card) : Ps.card ≤ 2 * (2 - 1 + 1) :=
  card_le_of_agree_ge α_injective le_rfl (by norm_num) (by norm_num) α (by norm_num) Ps hPs

-- The interpolation step: two points, `w = 1`, `D = 2`, `r = 1`; six monomials, two constraints.
example : ∃ Q : ℚ[X][X], Q ≠ 0 ∧ WeightedDegLE 1 2 Q ∧ ∀ i, HasRootMult Q (α i) (α i) 1 :=
  exists_interpolant α α 1 2 1 (by decide)

-- Multiplicity `r = 2` at three points with `w = 1`, `D = 3`: ten monomials, nine constraints.
example (y : Fin 3 → ℚ) : ∃ Q : ℚ[X][X], Q ≠ 0 ∧ WeightedDegLE 1 3 Q ∧
    ∀ i, HasRootMult Q (![0, 1, 2] i) (y i) 2 :=
  exists_interpolant ![0, 1, 2] y 1 3 2 (by decide)

-- The number of multiplicity constraints for `r = 3` is `C(4, 2) = 6`.
example : (lowMonomials 3).card = 6 := card_lowMonomials 3

-- The full decoder statement on the running example.
example : ∃ Q : ℚ[X][X], Q ≠ 0 ∧ WeightedDegLE 1 2 Q ∧ ∀ P : ℚ[X], P.natDegree ≤ 1 →
    2 < (Finset.univ.filter fun i => P.eval (α i) = α i).card * 1 → X - C P ∣ Q :=
  exists_interpolant_dvd α_injective α 1 2 1 (by decide)

-- At most `D / w = 1` polynomial divides `Q = Y - X`.
example (Ps : Finset ℚ[X]) (hPs : ∀ P ∈ Ps, X - C P ∣ Q) : Ps.card ≤ 1 / 1 := by
  have hQ0 : Q ≠ 0 := by
    intro h
    have := congrArg (fun R : ℚ[X][X] => R.coeff 1) h
    simp [Q_coeff_one] at this
  exact card_le_div_of_dvd le_rfl hQ0 Q_weightedDegLE Ps hPs

end Cslib.CodingTheory.GuruswamiSudanTests

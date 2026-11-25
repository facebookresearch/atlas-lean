/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.ClusterAlgebra.SomosFour
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Integrality of the Somos-4 sequence

Every term of the Somos-4 sequence is an integer. A conserved polynomial and coprimality of
adjacent terms give the divisibility needed at each step of the recurrence.
-/

public section

namespace MathlibExt.RingTheory.ClusterAlgebra.LaurentPhenomenonWanted

/-- A polynomial that vanishes on each block of four consecutive terms. -/
private def conservedPolynomial (a b c d : ℤ) : ℤ :=
  a ^ 2 * d ^ 2 + b ^ 2 * (b * d + c ^ 2) + a * c ^ 3 - 4 * a * b * c * d

private theorem dvd_of_conservedPolynomial_eq_zero {a b c d : ℤ} (hab : IsCoprime a b)
    (h : conservedPolynomial a b c d = 0) : a ∣ b * d + c ^ 2 := by
  apply (hab.pow_right (n := 2)).dvd_of_dvd_mul_left
  refine ⟨4 * b * c * d - a * d ^ 2 - c ^ 3, ?_⟩
  unfold conservedPolynomial at h
  linear_combination h

private theorem conservedPolynomial_step {a b c d e : ℤ} (ha : a ≠ 0)
    (h : conservedPolynomial a b c d = 0) (he : a * e = b * d + c ^ 2) :
    conservedPolynomial b c d e = 0 := by
  have hstep : a * conservedPolynomial b c d e = 0 := by
    unfold conservedPolynomial at h ⊢
    linear_combination e * h + (b ^ 2 * e - a * d ^ 2) * he
  exact (mul_eq_zero.mp hstep).resolve_left ha

/-- A sliding block of integer representatives with coprime neighbors and vanishing polynomial. -/
private theorem exists_integer_block (m : ℕ) :
    ∃ a b c d : ℤ, somos4 m = a ∧ somos4 (m + 1) = b ∧ somos4 (m + 2) = c ∧
      somos4 (m + 3) = d ∧ IsCoprime a b ∧ IsCoprime b c ∧ IsCoprime c d ∧
      conservedPolynomial a b c d = 0 := by
  induction m with
  | zero =>
    refine ⟨1, 1, 1, 1, ?_⟩
    norm_num [somos4, isCoprime_one_left, conservedPolynomial]
  | succ m ih =>
    obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hbc, hcd, h⟩ := ih
    obtain ⟨e, he⟩ := dvd_of_conservedPolynomial_eq_zero hab h
    have hde : IsCoprime d e := by
      have hmul : IsCoprime (a * e) d := by
        rw [← he, add_comm]
        exact (hcd.pow_left (m := 2)).add_mul_right_left b
      exact hmul.of_mul_left_right.symm
    have ha₀ : (a : ℚ) ≠ 0 := ha ▸ (somos4_pos m).ne'
    have he_cast : (d : ℚ) * (b : ℚ) + (c : ℚ) ^ 2 = (e : ℚ) * (a : ℚ) := by
      rw [mul_comm (d : ℚ), mul_comm (e : ℚ)]
      exact_mod_cast he
    have hnext : somos4 (m + 4) = e := by
      have hrec := somos4_add_four_mul m
      rw [ha, hb, hc, hd, he_cast] at hrec
      exact mul_right_cancel₀ ha₀ hrec
    have ha_int : a ≠ 0 := by exact_mod_cast ha₀
    exact ⟨b, c, d, e, hb, hc, hd, hnext, hbc, hcd, hde,
      conservedPolynomial_step ha_int h he.symm⟩

/-- **Integrality of the Somos-4 sequence.** Every term of the Somos-4 sequence
`1, 1, 1, 1, 2, 3, 7, 23, 59, …` is an integer (Fomin, Williams and Zelevinsky, *Introduction to
cluster algebras, Chapters 1–3*, arXiv:1608.05735v5, Example 3.4.3, deduced there from the
Laurent phenomenon; Fomin and Zelevinsky, *The Laurent phenomenon*, Adv. in Appl. Math. 28
(2002), Example 3.3, Laurentness of the generalized Somos-4 recurrence). -/
theorem somos4_isInt (m : ℕ) : ∃ z : ℤ, somos4 m = z := by
  obtain ⟨a, _, _, _, ha, _⟩ := exists_integer_block m
  exact ⟨a, ha⟩

end MathlibExt.RingTheory.ClusterAlgebra.LaurentPhenomenonWanted

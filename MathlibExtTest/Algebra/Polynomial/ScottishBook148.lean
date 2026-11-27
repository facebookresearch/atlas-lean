/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.ScottishBook148
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.Linarith

open MathlibExt.Algebra.Polynomial.ScottishBook148Wanted MvPolynomial
open scoped Polynomial

-- The zero-dimensional case has no coordinate lines to traverse.
example : IsConnected {x : Fin 0 → ℝ | eval x (1 : MvPolynomial (Fin 0) ℝ) ≠ 0} := by
  apply (auerbachPolynomialZeroSetSeparatesIffFactorsSignDefinite 0 1 one_ne_zero).mpr
  intro Q hQ hdiv
  exact (hQ.not_isUnit (isUnit_of_dvd_one hdiv)).elim

-- Squaring the coordinate hides its sign change but leaves the complement disconnected.
example : ¬ IsConnected {x : Fin 1 → ℝ | eval x ((X 0 : MvPolynomial (Fin 1) ℝ) ^ 2) ≠ 0} := by
  intro h
  let Q : MvPolynomial (Fin 1) ℝ := X 0
  have hQ : Irreducible Q := (prime_X (R := ℝ) (i := (0 : Fin 1))).irreducible
  have hdiv : Q ∣ Q ^ 2 := dvd_pow_self Q (by decide)
  rcases (auerbachPolynomialZeroSetSeparatesIffFactorsSignDefinite 1 (Q ^ 2)
    (pow_ne_zero _ hQ.ne_zero)).mp h Q hQ hdiv with hnonneg | hnonpos
  · have hneg := hnonneg (fun _ ↦ -1)
    norm_num [Q] at hneg
  · have hpos := hnonpos (fun _ ↦ 1)
    norm_num [Q] at hpos

-- A root-free quadratic has a connected complement. Its irreducible divisors
-- are scalar multiples, so both possible signs of the scalar are allowed.
example : IsConnected {x : Fin 1 → ℝ |
    eval x ((X 0 : MvPolynomial (Fin 1) ℝ) ^ 2 + 1) ≠ 0} := by
  let p : MvPolynomial (Fin 1) ℝ := X 0 ^ 2 + 1
  let e := uniqueAlgEquiv ℝ (Fin 1)
  have hep : e p = (Polynomial.X : ℝ[X]) ^ 2 + 1 := by
    simp [e, p, uniqueAlgEquiv_apply]
  have hp' : Irreducible (e p) := by
    rw [hep]
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · change ((Polynomial.X : ℝ[X]) ^ 2 + Polynomial.C 1).natDegree ∈ Finset.Icc 1 3
      simp
    · intro t ht
      have ht' : t ^ 2 + 1 = 0 := by simpa [Polynomial.IsRoot] using ht
      linarith [sq_nonneg t]
  have hp : Irreducible p := by
    have hirr := hp'.map e.symm.toMulEquiv
    change Irreducible (e.symm (e p)) at hirr
    rwa [AlgEquiv.symm_apply_apply] at hirr
  apply (auerbachPolynomialZeroSetSeparatesIffFactorsSignDefinite 1 p hp.ne_zero).mpr
  intro Q hQ hdiv
  obtain ⟨u, hu⟩ := ((hQ.dvd_irreducible_iff_associated hp).mp hdiv).symm
  obtain ⟨r, _, hr⟩ := isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  have hEval (x : Fin 1 → ℝ) : eval x Q = (x 0 ^ 2 + 1) * r := by
    rw [← hu, hr]
    simp [p]
  rcases le_total 0 r with hr' | hr'
  · exact Or.inl fun x ↦ hEval x ▸ mul_nonneg (by positivity) hr'
  · exact Or.inr fun x ↦ hEval x ▸ mul_nonpos_of_nonneg_of_nonpos (by positivity) hr'

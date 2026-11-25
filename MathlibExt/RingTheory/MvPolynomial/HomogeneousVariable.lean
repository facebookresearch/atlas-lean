/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogeneous projection under multiplication by a polynomial variable

Multiplication by a variable raises coefficient degree by exactly one.
Projection to degree zero therefore annihilates its image. The proof uses
the original monomial basis and works over an arbitrary commutative semiring.
-/

@[expose] public section

namespace MvPolynomial

universe u v

variable {R : Type u} [CommSemiring R] {I : Type v}

/-- Projection through multiplication by an actual polynomial variable shifts
the homogeneous degree by one. -/
theorem homogeneousComponent_mul_X (d : ℕ) (p : MvPolynomial I R) (i : I) :
    homogeneousComponent (d + 1) (p * X i) = homogeneousComponent d p * X i := by
  induction p using MvPolynomial.induction_on' with
  | monomial e r =>
      have hmul : monomial e r * X i = monomial (e + Finsupp.single i 1) r := by
        rw [monomial_add_single, pow_one]
      have hdegree : (e + Finsupp.single i 1).degree = e.degree + 1 := by
        rw [map_add, Finsupp.degree_single]
      have hnew : (monomial (e + Finsupp.single i 1) r).IsHomogeneous (e.degree + 1) :=
        isHomogeneous_monomial r hdegree
      have hold : (monomial e r).IsHomogeneous e.degree := isHomogeneous_monomial r rfl
      rw [hmul, homogeneousComponent_of_mem hnew, homogeneousComponent_of_mem hold]
      by_cases h : d = e.degree
      · subst d
        rw [if_pos rfl, if_pos rfl]
        exact hmul.symm
      · have h' : d + 1 ≠ e.degree + 1 := fun heq => h (Nat.add_right_cancel heq)
        rw [if_neg h', if_neg h, zero_mul]
  | add p q hp hq =>
      simp only [add_mul, map_add, hp, hq]

/-- The coefficient-degree-zero projection kills the image of multiplication
by every actual polynomial variable. -/
theorem homogeneousComponent_zero_mul_X (p : MvPolynomial I R) (i : I) :
    homogeneousComponent 0 (p * X i) = 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial e r =>
      have hmul : monomial e r * X i = monomial (e + Finsupp.single i 1) r := by
        rw [monomial_add_single, pow_one]
      have hdegree : (e + Finsupp.single i 1).degree = e.degree + 1 := by
        rw [map_add, Finsupp.degree_single]
      rw [hmul, homogeneousComponent_of_mem (isHomogeneous_monomial r hdegree)]
      rw [if_neg (by omega)]
  | add p q hp hq =>
      simp only [add_mul, map_add, hp, hq, add_zero]

/-- An actual homogeneous projection lies in the native total-degree cutoff. -/
theorem homogeneousComponent_mem_restrictTotalDegree (d : ℕ) (p : MvPolynomial I R) :
    homogeneousComponent d p ∈ restrictTotalDegree I R d := by
  rw [restrictTotalDegree, mem_restrictSupport_iff]
  intro e he
  have hcoeff := mem_support_iff.mp he
  rw [coeff_homogeneousComponent] at hcoeff
  split_ifs at hcoeff with h
  · exact le_of_eq h
  · exact (hcoeff rfl).elim

theorem IsHomogeneous.mem_restrictTotalDegree {d : ℕ} {p : MvPolynomial I R}
    (hp : p.IsHomogeneous d) : p ∈ restrictTotalDegree I R d := by
  rw [← homogeneousComponent_eq_self hp]
  exact homogeneousComponent_mem_restrictTotalDegree d p

/-- On the native degree-`q+1` cutoff, the highest component vanishes exactly
on the previous degree cutoff. This also covers the zero coefficient ring. -/
theorem mem_restrictTotalDegree_iff_highestComponent_zero (q : ℕ) (p : MvPolynomial I R)
    (hp : p ∈ restrictTotalDegree I R (q + 1)) :
    p ∈ restrictTotalDegree I R q ↔ homogeneousComponent (q + 1) p = 0 := by
  constructor
  · intro hlow
    apply homogeneousComponent_eq_zero' (q + 1) p
    intro e he
    have heq : e.degree ≤ q := by
      rw [restrictTotalDegree, mem_restrictSupport_iff] at hlow
      exact hlow he
    omega
  · intro hzero
    rw [restrictTotalDegree, mem_restrictSupport_iff]
    intro e he
    have heq : e.degree ≤ q + 1 := by
      rw [restrictTotalDegree, mem_restrictSupport_iff] at hp
      exact hp he
    have hne : e.degree ≠ q + 1 := by
      intro hdegree
      have h := congrArg (fun r : MvPolynomial I R => r.coeff e) hzero
      have hcoeff : p.coeff e = 0 := by
        simpa [coeff_homogeneousComponent, hdegree] using h
      exact (mem_support_iff.mp he) hcoeff
    change e.degree ≤ q
    omega

end MvPolynomial

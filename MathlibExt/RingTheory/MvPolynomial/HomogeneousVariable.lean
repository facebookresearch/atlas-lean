/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogeneous projections and multiplication by a polynomial variable

Let R be a commutative semiring and I an arbitrary variable set. Multiplication by Xᵢ shifts the
homogeneous decomposition by one: the degree-(d+1) component of pXᵢ is the degree-d component of
p multiplied by Xᵢ, and the degree-zero component is zero.

Every degree-d component belongs to the total-degree≤d polynomial submodule. If p has total
degree bounded by q+1 in this support sense, it belongs to the previous cutoff q exactly when
its degree-(q+1) homogeneous component is zero. These statements include the zero polynomial and
zero coefficient semiring, without a nontriviality assumption.
-/

@[expose] public section

namespace MvPolynomial

universe u v

variable {R : Type u} [CommSemiring R] {I : Type v}

/-- For a commutative semiring R, arbitrary variable set I, d : ℕ, p∈R[I] and i∈I,
π_{d+1}(pXᵢ)=π_d(p)Xᵢ, where π_d is the total homogeneous-degree projection. -/
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

/-- For a commutative semiring R, arbitrary I, p∈R[I] and i∈I, π₀(pXᵢ)=0. This includes p=0 and a
trivial coefficient semiring. -/
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

/-- For a commutative semiring R, arbitrary I, d : ℕ and p∈R[I], π_d(p) belongs to
restrictTotalDegree I R d: every monomial in its support has total degree at most d. -/
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

/-- For a commutative semiring R, arbitrary I, q : ℕ and p whose support has total degree at most
q+1, p has support degree at most q if and only if π_{q+1}(p)=0. The upper-cutoff hypothesis is
required, and no nontriviality condition on R is imposed. -/
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

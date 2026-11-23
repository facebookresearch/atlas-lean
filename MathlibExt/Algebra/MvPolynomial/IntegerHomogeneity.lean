/-
Copyright 2026 Anthropic, PBC
Released under the Apache License, Version 2.0.

Adapted from Fermat's Last Theorem in Lean 4, revision
6e837e75355538c7f80bab5b956861e86c4eacc2:
P2M/Sol/S_MvPolynomial_isHomogeneous_of_forall_eval_intCast_mul_eq_pow_mul.lean
Theorems/Thm_MvPolynomial_isHomogeneous_of_forall_eval_intCast_mul_eq_pow_mul.lean
The frozen files name no individual authors; copyright is from their NOTICE.
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Homogeneity from integer-grid scaling

A polynomial is homogeneous of degree `d` if scaling every integer grid point
by every integer scales its value by the `d`th power. No finiteness assumption
on the variables is needed. Zero remains homogeneous of every degree.
-/

public section

namespace MvPolynomial

private lemma eq_of_eval_intCast {R : Type*} [CommRing R] [IsDomain R]
    [CharZero R] {ι : Type*} {p q : MvPolynomial ι R}
    (h : ∀ c : ι → ℤ, eval (fun i => (c i : R)) p =
      eval (fun i => (c i : R)) q) : p = q := by
  apply funext_set (fun _ => Set.range (Int.cast : ℤ → R))
    (fun _ => Set.infinite_range_of_injective Int.cast_injective)
  intro x hx
  choose c hc using fun i => hx i (Set.mem_univ i)
  have hx' : x = fun i => (c i : R) := _root_.funext fun i => (hc i).symm
  subst x
  exact h c

private lemma eval_scale_of_homogeneous {R : Type*} [CommSemiring R]
    {ι : Type*} {p : MvPolynomial ι R} {d : ℕ}
    (hp : p.IsHomogeneous d) (t : R) (x : ι → R) :
    eval (fun i => t * x i) p = t ^ d * eval x p := by
  simp only [eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← hp.degree_eq_sum_deg_support hm]
  ac_rfl

private lemma component_polynomial_eq {R : Type*} [CommRing R]
    [IsDomain R] [CharZero R] {ι : Type*} (p : MvPolynomial ι R) (d : ℕ)
    (h : ∀ (n : ℤ) (c : ι → ℤ), eval (fun i => ((n * c i : ℤ) : R)) p =
      (n : R) ^ d * eval (fun i => (c i : R)) p) (c : ι → ℤ) :
    (∑ j ∈ Finset.range (p.totalDegree + 1),
      Polynomial.C (eval (fun i => (c i : R)) (homogeneousComponent j p)) *
        Polynomial.X ^ j) =
      Polynomial.C (eval (fun i => (c i : R)) p) * Polynomial.X ^ d := by
  classical
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := Set.range (Int.cast : ℤ → R)) ?_
    (Set.infinite_range_of_injective Int.cast_injective)
  rintro _ ⟨n, rfl⟩
  have he : eval (fun i => ((n * c i : ℤ) : R)) p =
      ∑ j ∈ Finset.range (p.totalDegree + 1),
        (n : R) ^ j * eval (fun i => (c i : R)) (homogeneousComponent j p) := by
    conv_lhs => rw [← sum_homogeneousComponent p, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    simpa only [Int.cast_mul] using
      eval_scale_of_homogeneous (homogeneousComponent_isHomogeneous j p)
        (n : R) (fun i => (c i : R))
  simpa only [Set.mem_ofPred_eq, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
    using he.symm.trans (h n c)

/-- Integer-grid scaling detects formal homogeneity over a characteristic-zero
integral domain. The variable type need not be finite or nonempty. -/
theorem isHomogeneous_of_forall_eval_intCast_mul_eq_pow_mul
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {ι : Type*}
    (P : MvPolynomial ι R) (d : ℕ)
    (h : ∀ (n : ℤ) (c : ι → ℤ), eval (fun i => ((n * c i : ℤ) : R)) P =
      (n : R) ^ d * eval (fun i => (c i : R)) P) :
    P.IsHomogeneous d := by
  classical
  have hcomp (k : ℕ) (hkd : k ≠ d) : homogeneousComponent k P = 0 := by
    by_cases hk : P.totalDegree < k
    · exact homogeneousComponent_eq_zero k P hk
    apply eq_of_eval_intCast
    intro c
    have hc := congrArg (fun q : Polynomial R => q.coeff k)
      (component_polynomial_eq P d h c)
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] at hc
    rw [Finset.sum_ite_eq,
      ite_eq_left (Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Nat.le_of_not_gt hk))),
      ite_eq_right hkd] at hc
    simpa only [map_zero] using hc
  have hP : P = homogeneousComponent d P := by
    conv_lhs => rw [← sum_homogeneousComponent P]
    rw [Finset.sum_eq_single d (fun k _ hk => hcomp k hk)]
    intro hd
    rw [Finset.mem_range, not_lt] at hd
    exact homogeneousComponent_eq_zero d P (Nat.lt_of_succ_le hd)
  rw [hP]
  exact homogeneousComponent_isHomogeneous d P

end MvPolynomial

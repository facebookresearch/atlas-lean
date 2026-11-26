/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.RingTheory.MvPolynomial.HomogeneousVariable

/-!
# Highest homogeneous components under degree bounds

Let `R` be any commutative ring and `I` a variable type in an independent universe. The strict
total-degree submodule consists of multivariate polynomials supported on exponent vectors of
degree less than `n`. It is zero at `n = 0` and equals the usual degree-at-most-`n` submodule
at strict bound `n + 1`.

Multiplication by a monomial of degree `d` raises a strict bound `n` to `n + d`. If `p` and
`q` have total-degree bounds `n` and `m`, respectively, then `homogeneousComponent (n + m) (p
* q) = homogeneousComponent n p * homogeneousComponent m q`. The statement permits zero
highest components and arbitrary commutative coefficient rings.
-/

@[expose] public section

noncomputable section

universe u v

namespace MvPolynomial

variable {R : Type u} [CommRing R] {I : Type v}

/-- Submodule of polynomials with strict total-degree support bound.

For natural `n`, `restrictStrictTotalDegree I R n` is the submodule of `MvPolynomial I R`
supported on exponent vectors `e` satisfying `e.degree < n`. -/
def restrictStrictTotalDegree (I : Type v) (R : Type u) [CommRing R] (n : ℕ) :
    Submodule R (MvPolynomial I R) :=
  restrictSupport R {e | e.degree < n}

/-- Strict total-degree support submodules are monotone.

If `n ≤ m`, every polynomial supported in total degrees less than `n` is supported in total
degrees less than `m`. -/
theorem restrictStrictTotalDegree_mono :
    Monotone (restrictStrictTotalDegree I R) := by
  intro n m hnm
  exact restrictSupport_mono R fun e he => he.trans_le hnm

/-- Strict degree-zero submodule is zero.

The submodule of polynomials supported in total degrees less than zero is `⊥`. -/
@[simp]
theorem restrictStrictTotalDegree_zero : restrictStrictTotalDegree I R 0 = ⊥ := by
  rw [restrictStrictTotalDegree, show {e : I →₀ ℕ | e.degree < 0} = ∅ by
    ext e
    simp]
  rw [restrictSupport_eq_span]
  simp only [Set.image_empty, Submodule.span_empty]

/-- Strict successor bound equals a weak degree bound.

For natural `n`, `restrictStrictTotalDegree I R (n + 1) = restrictTotalDegree I R n`, since
natural exponent degrees satisfy `d < n + 1` exactly when `d ≤ n`. -/
@[simp]
theorem restrictStrictTotalDegree_succ (n : ℕ) :
    restrictStrictTotalDegree I R (n + 1) = restrictTotalDegree I R n := by
  apply congrArg (restrictSupport R)
  ext e
  change e.degree < n + 1 ↔ e.degree ≤ n
  exact Nat.lt_succ_iff

/-- Component at a strict support bound vanishes.

If `p` lies in `restrictStrictTotalDegree I R n`, then its degree-`n` homogeneous component is
zero. -/
theorem homogeneousComponent_eq_zero_of_mem_strict {n : ℕ} {p : MvPolynomial I R}
    (hp : p ∈ restrictStrictTotalDegree I R n) : homogeneousComponent n p = 0 := by
  apply homogeneousComponent_eq_zero' n p
  intro e he
  rw [restrictStrictTotalDegree, mem_restrictSupport_iff] at hp
  exact ne_of_lt (hp he)

/-- Weak degree bound gives the next strict bound.

If `p` lies in `restrictTotalDegree I R n`, then `p` lies in `restrictStrictTotalDegree I R (n
+ 1)`. -/
theorem mem_strict_succ_of_mem_degree {n : ℕ} {p : MvPolynomial I R}
    (hp : p ∈ restrictTotalDegree I R n) :
    p ∈ restrictStrictTotalDegree I R (n + 1) := by
  simpa only [restrictStrictTotalDegree_succ] using hp

/-- Degree-zero bounded polynomial equals its constant component.

If `p` is supported in total degree at most zero, then `homogeneousComponent 0 p = p`. -/
theorem homogeneousComponent_zero_eq_self_of_mem_degree_zero {p : MvPolynomial I R}
    (hp : p ∈ restrictTotalDegree I R 0) : homogeneousComponent 0 p = p := by
  ext e
  rw [coeff_homogeneousComponent]
  by_cases he : p.coeff e = 0
  · simp only [he, ite_self]
  · rw [restrictTotalDegree, mem_restrictSupport_iff] at hp
    have hdegree : e.degree = 0 := Nat.le_zero.mp (hp (mem_support_iff.mpr he))
    rw [if_pos hdegree]

/-- Monomial multiplication raises a strict support bound by its degree.

If `p` has support in total degrees less than `n`, then for an exponent vector `e : I →₀ ℕ`
and coefficient `r : R`, the product `p * monomial e r` has support in degrees less than `n +
e.degree`. -/
theorem mul_monomial_mem_strict {n : ℕ} {p : MvPolynomial I R}
    (hp : p ∈ restrictStrictTotalDegree I R n) (e : I →₀ ℕ) (r : R) :
    p * monomial e r ∈ restrictStrictTotalDegree I R (n + e.degree) := by
  rw [restrictStrictTotalDegree, restrictSupport_eq_span] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨f, hf, rfl⟩ := hp
      rw [monomial_mul_monomial, one_mul, restrictStrictTotalDegree,
        monomial_mem_restrictSupport]
      exact Or.inl (by
        change (f + e).degree < n + e.degree
        change f.degree < n at hf
        rw [map_add]
        omega)
  | zero =>
      rw [zero_mul]
      exact (restrictStrictTotalDegree I R (n + e.degree)).zero_mem
  | add p q hp hq ihp ihq =>
      rw [add_mul]
      exact (restrictStrictTotalDegree I R (n + e.degree)).add_mem ihp ihq
  | smul c p hp ih =>
      rw [smul_mul_assoc]
      exact (restrictStrictTotalDegree I R (n + e.degree)).smul_mem c ih

private def highestProductDefect (n m : ℕ) :
    MvPolynomial I R →ₗ[R] MvPolynomial I R →ₗ[R] MvPolynomial I R where
  toFun p :=
    { toFun := fun q => homogeneousComponent (n + m) (p * q) -
        homogeneousComponent n p * homogeneousComponent m q
      map_add' q r := by
        simp only [mul_add, map_add, add_sub_add_comm]
      map_smul' c q := by
        simp only [mul_smul_comm, map_smul, smul_sub, RingHom.id_apply] }
  map_add' p q := by
    apply LinearMap.ext
    intro r
    change homogeneousComponent (n + m) ((p + q) * r) -
        homogeneousComponent n (p + q) * homogeneousComponent m r =
      (homogeneousComponent (n + m) (p * r) - homogeneousComponent n p * homogeneousComponent m r) +
        (homogeneousComponent (n + m) (q * r) - homogeneousComponent n q * homogeneousComponent m r)
    simp only [add_mul, map_add, LinearMap.add_apply, add_sub_add_comm]
  map_smul' c p := by
    apply LinearMap.ext
    intro q
    change homogeneousComponent (n + m) ((c • p) * q) -
        homogeneousComponent n (c • p) * homogeneousComponent m q =
      (RingHom.id R) c •
        (homogeneousComponent (n + m) (p * q) - homogeneousComponent n p * homogeneousComponent m q)
    simp only [smul_mul_assoc, map_smul, LinearMap.smul_apply, smul_sub, RingHom.id_apply]

private theorem highestProductDefect_monomial (n m : ℕ) (e f : I →₀ ℕ)
    (he : e.degree ≤ n) (hf : f.degree ≤ m) :
    highestProductDefect (R := R) n m (monomial e 1) (monomial f 1) = 0 := by
  change homogeneousComponent (n + m) (monomial e (1 : R) * monomial f 1) -
    homogeneousComponent n (monomial e 1) * homogeneousComponent m (monomial f 1) = 0
  rw [monomial_mul_monomial, one_mul,
    homogeneousComponent_of_mem (isHomogeneous_monomial (1 : R)
      (show (e + f).degree = e.degree + f.degree from map_add Finsupp.degree e f)),
    homogeneousComponent_of_mem (isHomogeneous_monomial (1 : R) (rfl : e.degree = e.degree)),
    homogeneousComponent_of_mem (isHomogeneous_monomial (1 : R) (rfl : f.degree = f.degree))]
  by_cases hen : n = e.degree
  · by_cases hfm : m = f.degree
    · rw [if_pos (by omega), if_pos hen, if_pos hfm, monomial_mul_monomial, one_mul, sub_self]
    · rw [if_neg (by omega), if_pos hen, if_neg hfm, mul_zero, sub_self]
  · by_cases hfm : m = f.degree
    · rw [if_neg (by omega), if_neg hen, if_pos hfm, zero_mul, sub_self]
    · rw [if_neg (by omega), if_neg hen, if_neg hfm, zero_mul, sub_self]

/-- Highest allowed component of a product is the product of highest components.

If `p` is supported in total degrees at most `n` and `q` in degrees at most `m`, then the
degree-`n + m` component of `p * q` equals the product of the degree-`n` component of `p` and
the degree-`m` component of `q`. -/
theorem homogeneousComponent_mul_of_degreeBounds (n m : ℕ)
    (p q : MvPolynomial I R)
    (hp : p ∈ restrictTotalDegree I R n) (hq : q ∈ restrictTotalDegree I R m) :
    homogeneousComponent (n + m) (p * q) =
      homogeneousComponent n p * homogeneousComponent m q := by
  have hzero : highestProductDefect n m p q = 0 := by
    rw [restrictTotalDegree, restrictSupport_eq_span] at hp hq
    induction hp using Submodule.span_induction with
    | mem p hp =>
        obtain ⟨e, he, rfl⟩ := hp
        induction hq using Submodule.span_induction with
        | mem q hq =>
            obtain ⟨f, hf, rfl⟩ := hq
            exact highestProductDefect_monomial n m e f he hf
        | zero => simp only [map_zero]
        | add q r hq hr ihq ihr =>
            simp only [map_add, ihq, ihr, add_zero]
        | smul c q hq ih =>
            simp only [map_smul, ih, smul_zero]
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add p r hp hr ihp ihr =>
        simp only [map_add, LinearMap.add_apply, ihp, ihr, add_zero]
    | smul c p hp ih =>
        simp only [map_smul, LinearMap.smul_apply, ih, smul_zero]
  exact sub_eq_zero.mp hzero

end MvPolynomial

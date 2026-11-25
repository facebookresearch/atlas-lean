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
# Leading products at an actual polynomial degree bound

The strict degree submodule includes degree zero without a truncated
predecessor. Multiplication by a monomial raises its bound by the monomial
degree. On two actual degree cutoffs, the component in the sum degree is
the product of the two highest components. All proofs use native monomial
spans and allow an arbitrary commutative coefficient ring.
-/

@[expose] public section

noncomputable section

universe u v

namespace MvPolynomial

variable {R : Type u} [CommRing R] {I : Type v}

/-- Polynomials supported strictly below the indicated degree. -/
def restrictStrictTotalDegree (I : Type v) (R : Type u) [CommRing R] (n : ℕ) :
    Submodule R (MvPolynomial I R) :=
  restrictSupport R {e | e.degree < n}

theorem restrictStrictTotalDegree_mono :
    Monotone (restrictStrictTotalDegree I R) := by
  intro n m hnm
  exact restrictSupport_mono R fun e he => he.trans_le hnm

@[simp]
theorem restrictStrictTotalDegree_zero : restrictStrictTotalDegree I R 0 = ⊥ := by
  rw [restrictStrictTotalDegree, show {e : I →₀ ℕ | e.degree < 0} = ∅ by
    ext e
    simp]
  rw [restrictSupport_eq_span]
  simp only [Set.image_empty, Submodule.span_empty]

@[simp]
theorem restrictStrictTotalDegree_succ (n : ℕ) :
    restrictStrictTotalDegree I R (n + 1) = restrictTotalDegree I R n := by
  apply congrArg (restrictSupport R)
  ext e
  change e.degree < n + 1 ↔ e.degree ≤ n
  exact Nat.lt_succ_iff

/-- A strict upper bound annihilates the component at that bound. -/
theorem homogeneousComponent_eq_zero_of_mem_strict {n : ℕ} {p : MvPolynomial I R}
    (hp : p ∈ restrictStrictTotalDegree I R n) : homogeneousComponent n p = 0 := by
  apply homogeneousComponent_eq_zero' n p
  intro e he
  rw [restrictStrictTotalDegree, mem_restrictSupport_iff] at hp
  exact ne_of_lt (hp he)

/-- An actual degree cutoff lies strictly below its successor. -/
theorem mem_strict_succ_of_mem_degree {n : ℕ} {p : MvPolynomial I R}
    (hp : p ∈ restrictTotalDegree I R n) :
    p ∈ restrictStrictTotalDegree I R (n + 1) := by
  simpa only [restrictStrictTotalDegree_succ] using hp

/-- The degree-zero cutoff consists of its own homogeneous component. -/
theorem homogeneousComponent_zero_eq_self_of_mem_degree_zero {p : MvPolynomial I R}
    (hp : p ∈ restrictTotalDegree I R 0) : homogeneousComponent 0 p = p := by
  ext e
  rw [coeff_homogeneousComponent]
  by_cases he : p.coeff e = 0
  · simp only [he, ite_self]
  · rw [restrictTotalDegree, mem_restrictSupport_iff] at hp
    have hdegree : e.degree = 0 := Nat.le_zero.mp (hp (mem_support_iff.mpr he))
    rw [if_pos hdegree]

/-- Multiplication by a monomial raises a strict degree bound by its degree. -/
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

/-- Multiplication in the sum degree is the product of the original highest
components, provided each original polynomial satisfies its degree bound. -/
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

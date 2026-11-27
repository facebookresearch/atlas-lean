/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Support and top coefficients under polynomial translation

Substitution of `X i + C (a i)` for `X i` is triangular in the coordinatewise order
on exponents: each monomial contributes only to its divisors, with its original coefficient
on the diagonal. Thus a model may specify a lower set of *allowed* exponents without
requiring the nonzero coefficients of any one polynomial to form a lower set.

See Martini et al., Proposition 1, Definition 1 and the appendix proof of Proposition 1,
<https://doi.org/10.1534/g3.118.200961>.
-/

namespace MvPolynomial

variable {σ R : Type*}

local notation:max "shift " a:arg => aeval (fun i => X i + C (a i))

section Semiring

variable [CommSemiring R]

private theorem translated_monomial (a : σ → R) (m : σ →₀ ℕ) (c : R) :
    (∀ e ∈ (shift a (monomial m c)).support, e ≤ m) ∧
      (shift a (monomial m c)).coeff m = c := by
  classical
  obtain ⟨s, rfl⟩ := Multiset.toFinsupp.surjective m
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.toFinsupp_zero, ← C_apply, aeval_C, algebraMap_eq]
    exact ⟨fun e he => (Finset.mem_singleton.mp (support_monomial_subset he)).le, coeff_zero_C _⟩
  | cons i s ih =>
    rw [← Multiset.singleton_add, add_comm ({i} : Multiset σ) s, map_add,
      Multiset.toFinsupp_singleton, monomial_add_single, pow_one, map_mul, aeval_X, mul_add]
    let q := shift a (monomial s.toFinsupp c)
    change (∀ e ∈ (q * X i + q * C (a i)).support, _) ∧ _
    obtain ⟨hs, hc⟩ := ih
    have hz : q.coeff (s.toFinsupp + Finsupp.single i 1) = 0 := by
      apply notMem_support_iff.mp
      intro he
      have hi := hs _ he i
      simp at hi
    constructor
    · intro e he
      rcases Finset.mem_union.mp (support_add he) with hx | ha
      · rw [support_mul_X] at hx
        obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hx
        exact add_le_add_left (hs k hk) _
      · rw [mul_comm, mem_support_iff, coeff_C_mul] at ha
        exact (hs _ (mem_support_iff.mpr (right_ne_zero_of_mul ha))).trans le_self_add
    · change (q * X i + q * C (a i)).coeff _ = c
      rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_mul_X, mul_comm q (C _),
        coeff_C_mul, hz, mul_zero, add_zero, hc]

/-- Translating the variables of a polynomial over a commutative semiring preserves every
coefficient whose exponent has total degree at least the polynomial's total degree. This
includes absent monomials; no hypothesis about which lower coefficients vanish is needed. -/
public theorem coeff_aeval_X_add_C_of_totalDegree_le (p : MvPolynomial σ R) (a : σ → R)
    (d : σ →₀ ℕ) (hd : p.totalDegree ≤ d.degree) :
    (shift a p).coeff d = p.coeff d := by
  classical
  calc
    _ = ∑ e ∈ p.support, (shift a (monomial e (p.coeff e))).coeff d := by
      conv_lhs => rw [p.as_sum, map_sum, coeff_sum]
    _ = (shift a (monomial d (p.coeff d))).coeff d := by
      apply Finset.sum_eq_single
      · intro e he hne
        apply notMem_support_iff.mp
        intro h
        have hlt := Finsupp.degree_strictMono
          (lt_of_le_of_ne ((translated_monomial a e _).1 d h) hne.symm)
        exact hlt.not_ge ((le_totalDegree he).trans hd)
      · intro h
        simp [notMem_support_iff.mp h]
    _ = _ := (translated_monomial a d _).2

/-- For a multivariate polynomial over a commutative semiring of total degree at most `D`,
translation by any vector leaves its entire homogeneous component of degree `D` unchanged. -/
public theorem homogeneousComponent_aeval_X_add_C (p : MvPolynomial σ R) (a : σ → R)
    {D : ℕ} (hD : p.totalDegree ≤ D) :
    homogeneousComponent D (shift a p) = homogeneousComponent D p := by
  ext d
  simp only [coeff_homogeneousComponent]
  split_ifs with hd
  · exact coeff_aeval_X_add_C_of_totalDegree_le p a d (hd ▸ hD)
  · rfl

/-- If all exponents of a polynomial over a commutative semiring belong to an allowed set
closed under coordinatewise decrease, all exponents after translation also belong to it. -/
public theorem support_aeval_X_add_C_subset (p : MvPolynomial σ R) (a : σ → R)
    {S : Set (σ →₀ ℕ)} (hS : IsLowerSet S) (hp : ↑p.support ⊆ S) :
    ↑(shift a p).support ⊆ S := by
  classical
  intro d hd
  rw [p.as_sum, map_sum] at hd
  obtain ⟨e, he, hde⟩ := Finset.mem_biUnion.mp (support_sum hd)
  exact hS ((translated_monomial a e _).1 d hde) (hp he)

/-- Translating the variables of a polynomial over a commutative semiring does not change its
maximum total degree. This uses the convention that the zero polynomial has total degree zero. -/
public theorem totalDegree_aeval_X_add_C (p : MvPolynomial σ R) (a : σ → R) :
    (shift a p).totalDegree = p.totalDegree := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro d hd
    by_contra! hlt
    exact (mem_support_iff.mp hd) ((coeff_aeval_X_add_C_of_totalDegree_le p a d hlt.le).trans
      (coeff_eq_zero_of_totalDegree_lt hlt))
  · by_cases hp : p = 0
    · simp [hp]
    obtain ⟨d, hd, hdeg⟩ := Finset.exists_mem_eq_sup p.support (support_nonempty.mpr hp)
      (fun d => d.degree)
    change p.totalDegree = d.degree at hdeg
    rw [hdeg]
    apply le_totalDegree
    rw [mem_support_iff, coeff_aeval_X_add_C_of_totalDegree_le p a d hdeg.le]
    exact mem_support_iff.mp hd

end Semiring

/-- Over a commutative ring, translation by any vector is a bijection on the polynomials
whose support lies in a fixed lower set of allowed exponents. Its inverse is translation by
the negative vector; coefficients of the allowed monomials are free to vanish. -/
public theorem bijOn_aeval_X_add_C_of_isLowerSet [CommRing R] (a : σ → R)
    {S : Set (σ →₀ ℕ)} (hS : IsLowerSet S) :
    Set.BijOn (shift a) {p : MvPolynomial σ R | ↑p.support ⊆ S} {p | ↑p.support ⊆ S} := by
  have cancel (v : σ → R) (p : MvPolynomial σ R) : shift (-v) (shift v p) = p := by
    simp only [comp_aeval_apply, map_add, aeval_X, aeval_C, algebraMap_eq, Pi.neg_apply,
      map_neg, neg_add_cancel_right, aeval_X_left_apply]
  apply Set.InvOn.bijOn (f' := shift (-a))
  · exact ⟨fun p _ => cancel a p, fun p _ => by simpa only [neg_neg] using cancel (-a) p⟩
  · exact fun p hp => support_aeval_X_add_C_subset p a hS hp
  · exact fun p hp => support_aeval_X_add_C_subset p (-a) hS hp

end MvPolynomial

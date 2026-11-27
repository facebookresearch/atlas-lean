/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.GeomSum

/-!
# Polynomial sums inducing the identity on a finite field

We characterize when the polynomial with coefficient `h.eval n` at each degree
`1 ≤ n ≤ k` induces the identity on a finite field, for `k ≡ 1` modulo `p * (q - 1)`.
-/

set_option autoImplicit false

open Finset

namespace MathlibExt.Algebra.PermutationPolynomialsWanted

section

variable {K : Type*} [Field K] {p : ℕ} [CharP K p]

-- The block starting at p * i has the same coefficients as the first block and weight (c ^ p) ^ i.
private theorem sum_blocks (h : Polynomial K) (c : K) (m : ℕ) :
    (∑ n ∈ range (p * m), h.eval (n : K) * c ^ n) =
      (∑ i ∈ range m, (c ^ p) ^ i) * ∑ r ∈ range p, h.eval (r : K) * c ^ r := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ (fun i => (c ^ p) ^ i),
      add_mul, mul_sum _ _ ((c ^ p) ^ m)]
    congr 1
    apply sum_congr rfl
    intro r _
    simp [pow_add, pow_mul, mul_left_comm]

-- Sum a positive power over the prime subfield by summing over its units.
private theorem prime_subfield_moment [Fact p.Prime] {i : ℕ} (hi : 0 < i) :
    (∑ r ∈ range p, (r : K) ^ i) = if p - 1 ∣ i then -1 else 0 := by
  have hu : (∑ u : (ZMod p)ˣ, (u : ZMod p) ^ i) = ∑ r ∈ range p, (r : ZMod p) ^ i := by
    apply sum_bij_ne_zero (fun (u : (ZMod p)ˣ) _ _ => (u : ZMod p).val)
    · exact fun u _ _ => mem_range.mpr (ZMod.val_lt _)
    · exact fun a _ _ b _ _ e => Units.ext (ZMod.val_injective p e)
    · intro r hr h
      have hr₀ : (r : ZMod p) ≠ 0 := fun e => h (by rw [e, zero_pow hi.ne'])
      exact ⟨Units.mk0 (r : ZMod p) hr₀, mem_univ _, h, ZMod.val_cast_of_lt (mem_range.mp hr)⟩
    · simp
  rw [FiniteField.sum_pow_units, ZMod.card] at hu
  simpa only [map_sum, map_pow, map_natCast, apply_ite, map_neg, map_one, map_zero] using
    congrArg (ZMod.castHom (dvd_refl p) K) hu.symm

private theorem sum_prime_subfield_eval [Fact p.Prime] (h : Polynomial K) :
    (∑ r ∈ range p, h.eval (r : K)) =
      -∑ j ∈ Icc 1 (h.natDegree / (p - 1)), h.coeff (j * (p - 1)) := by
  have hd : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [sum_comm]
  simp_rw [← mul_sum]
  rw [sum_range_eq_add_Ico _ (Nat.succ_pos _), Nat.succ_eq_add_one, Ico_add_one_right_eq_Icc]
  simp only [pow_zero, sum_const, card_range, nsmul_one, CharP.cast_eq_zero, mul_zero, zero_add]
  rw [← sum_neg_distrib]
  calc
    _ = ∑ i ∈ (Icc 1 h.natDegree).filter (p - 1 ∣ ·), -h.coeff i := by
      rw [sum_filter]
      refine sum_congr rfl fun i hi => ?_
      rw [prime_subfield_moment (mem_Icc.mp hi).1]
      split <;> simp
    _ = _ := by
      symm
      apply sum_nbij' (· * (p - 1)) (· / (p - 1))
      · intro j hj
        obtain ⟨hj₁, hj₂⟩ := mem_Icc.mp hj
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hj₁ hd,
          (Nat.le_div_iff_mul_le hd).mp hj₂⟩, dvd_mul_left _ _⟩
      · intro i hi
        obtain ⟨hi, hdiv⟩ := mem_filter.mp hi
        obtain ⟨hi₁, hi₂⟩ := mem_Icc.mp hi
        exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hi₁ hdiv) hd,
          Nat.div_le_div_right hi₂⟩
      · exact fun j _ => Nat.mul_div_cancel j hd
      · exact fun i hi => Nat.div_mul_cancel (mem_filter.mp hi).2
      · exact fun _ _ => rfl

-- At a nonzero argument the two boundary terms with coefficient h(0) cancel.
private theorem eval_from_blocks (h : Polynomial K) (c : K) {m k : ℕ}
    (hk : k = p * m + 1) (hc : (c ^ p) ^ m = 1) :
    (∑ n ∈ Icc 1 k, h.eval (n : K) * c ^ n) =
      (∑ i ∈ range m, (c ^ p) ^ i) * (∑ r ∈ range p, h.eval (r : K) * c ^ r) +
        h.eval 1 * c := by
  subst k
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sub _ (by omega), sum_range_succ,
    sum_range_succ, sum_blocks]
  simp [pow_succ, pow_mul, hc]
  abel

end

@[expose] public section

set_option linter.unusedVariables false in
/-- **When $\sum_{n=1}^k h(n) X^n$ induces the identity on $\mathbb{F}_q$.** Let $p$ be a
prime, $\ell \ge 1$ and $q = p^\ell > 2$, and let $K$ be a finite field of characteristic
$p$ with $q$ elements. Let $k$ be a positive integer with $k \equiv 1 \pmod{p(q-1)}$ and
let $h \in K[X]$, with degree $d$ (taken to be $0$ when $h = 0$) and coefficient $h_i$ of
$X^i$. Then $\sum_{n=1}^{k} h(n)\,c^n = c$ for every $c \in K$ if and only if $h(1) = 1$
and either $k \equiv 1 \pmod{p^2}$ or $\sum_{j=1}^{\lfloor d/(p-1) \rfloor} h_{j(p-1)} = 0$.

Source: Zhiguo Ding and Michael E. Zieve, "Permutation
Polynomials of the Form `∑_{n=1}^k h(n) X^n`", Theorem 2. -/
theorem finiteField_sum_eval_mul_pow_eq_id_iff
    (K : Type*) [Field K] [Fintype K] (p ℓ : ℕ) [CharP K p]
    (hp : p.Prime) (hℓ : 0 < ℓ)
    (hcard : Fintype.card K = p ^ ℓ) (hq : 2 < p ^ ℓ)
    (k : ℕ) (hk : 0 < k)
    (hkcong : k % (p * (p ^ ℓ - 1)) = 1)
    (h : Polynomial K) :
    (∀ c : K, (∑ n ∈ Finset.Icc 1 k, h.eval (n : K) * c ^ n) = c) ↔
      h.eval 1 = 1 ∧
        (k % (p ^ 2) = 1 ∨
          (∑ j ∈ Finset.Icc 1 (h.natDegree / (p - 1)),
            h.coeff (j * (p - 1))) = 0) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let m := (Fintype.card K - 1) * (k / (p * (p ^ ℓ - 1)))
  have hkm : k = p * m + 1 := by
    simpa only [m, hcard, Nat.mul_assoc, hkcong] using (Nat.div_add_mod k (p * (p ^ ℓ - 1))).symm
  have hperiod (c : K) (hc : c ≠ 0) : (c ^ p) ^ m = 1 := by
    simp only [m, pow_mul,
      FiniteField.pow_card_sub_one_eq_one _ (pow_ne_zero p hc), one_pow]
  let f (c : K) := ∑ n ∈ Icc 1 k, h.eval (n : K) * c ^ n
  let coeffSum := ∑ j ∈ Icc 1 (h.natDegree / (p - 1)), h.coeff (j * (p - 1))
  have hone : f 1 = h.eval 1 - (m : K) * coeffSum := by
    dsimp only [f]
    rw [eval_from_blocks h 1 hkm (by simp)]
    simp [sum_prime_subfield_eval (p := p), coeffSum, sub_eq_add_neg, add_comm]
  have hother (c : K) (hc : c ≠ 0) (hc₁ : c ≠ 1) : f c = h.eval 1 * c := by
    have hcp : c ^ p ≠ 1 := by
      intro he
      apply hc₁
      apply (frobenius K p).injective
      simpa [frobenius_def] using he
    dsimp only [f]
    rw [eval_from_blocks h c hkm (hperiod c hc), geom_sum_eq hcp, hperiod c hc]
    simp
  have hmod : (m : K) = 0 ↔ k % p ^ 2 = 1 := by
    have hp₂ : 1 < p ^ 2 := Nat.one_lt_pow (by decide) hp.one_lt
    rw [CharP.cast_eq_zero_iff K p, ← Nat.mod_eq_of_lt hp₂]
    change p ∣ m ↔ k ≡ 1 [MOD p ^ 2]
    rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' hk, hkm, Nat.add_sub_cancel, pow_two,
      Nat.mul_dvd_mul_iff_left hp.pos]
  change (∀ c, f c = c) ↔ h.eval 1 = 1 ∧ (k % p ^ 2 = 1 ∨ coeffSum = 0)
  constructor
  · intro hall
    obtain ⟨u, hu⟩ := Fintype.exists_ne_of_one_lt_card
      (α := Kˣ) (by rw [Fintype.card_units, hcard]; omega) 1
    have he : h.eval 1 = 1 := by
      apply mul_right_cancel₀ u.ne_zero
      rw [one_mul, ← hother u u.ne_zero (fun e => hu (Units.ext e)), hall]
    refine ⟨he, ?_⟩
    have hma : (m : K) * coeffSum = 0 := by
      simpa [hone, he] using hall 1
    exact (mul_eq_zero.mp hma).imp hmod.mp id
  · rintro ⟨he, ha⟩ c
    by_cases hc : c = 0
    · subst c
      exact sum_eq_zero fun n hn => by rw [zero_pow (Nat.ne_of_gt (mem_Icc.mp hn).1), mul_zero]
    by_cases hc₁ : c = 1
    · subst c
      rcases ha with hk₂ | ha
      · simp [hone, he, hmod.mpr hk₂]
      · simp [hone, he, ha]
    · rw [hother c hc hc₁, he, one_mul]

end

end MathlibExt.Algebra.PermutationPolynomialsWanted

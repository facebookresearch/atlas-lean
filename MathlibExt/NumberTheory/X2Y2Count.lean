/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.NatDivisors
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import MathlibExt.NumberTheory.ZsqrtdNegTwoEuclidean
public import MathlibExt.NumberTheory.ZsqrtdNegTwoPrimes
public import MathlibExt.NumberTheory.ZsqrtdNormFactorization
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Representation count for `x ^ 2 + 2 * y ^ 2`

The number `repX2Y2Count t` of elements of `ℤ[√-2]` of norm `t` equals twice
the divisor sum of the mod-8 character `ZMod.χ₈'`.

## References

The `x² + 2y²` formula is the discriminant `-8` case of Dirichlet's classical
formula for forms of class number one (two units, character `ZMod.χ₈'`). No
external text is adapted: the proof here is self-contained, by unique
factorization in `ℤ[√-2]`, through the ring-independent norm-fiber counts of
`MathlibExt.NumberTheory.ZsqrtdNormFactorization` at `d = -2`. The Euclidean
and prime-splitting infrastructure for `ℤ[√-2]` is developed in the
companion `Zsqrtd.NegTwo` namespace of `MathlibExt.NumberTheory.ZsqrtdNegTwoEuclidean`
and `MathlibExt.NumberTheory.ZsqrtdNegTwoPrimes`; no material is adapted
from the Gaussian norm-count development in
`MathlibExt/NumberTheory/ArithmeticFunction/FourTriangularNumbers.lean`.
-/

namespace SumSquares

open Zsqrtd.NegTwo (zsqrtd_neg_two_isUnit_iff zsqrtd_neg_two_prime_sqrtd zsqrtd_neg_two_inert
  zsqrtd_neg_two_split zsqrtd_neg_two_split_conj unitVal unitValInv unitVal_mul_unitValInv
  unitVal_inj unitVal_complete)

@[expose] public section

/-- `χ₋₂(1) = 1`. -/
public theorem chiNeg2_one : ZMod.χ₈' 1 = 1 := by decide

/-- The divisor sum of `χ₋₂`. -/
public noncomputable def divChiNeg2Sum (t : ℕ) : ℤ :=
  ∑ d ∈ Nat.divisors t, ZMod.χ₈' d

/-- Divisor sums of a completely multiplicative function are multiplicative. -/
public theorem divChiNeg2Sum_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    divChiNeg2Sum (m * n) = divChiNeg2Sum m * divChiNeg2Sum n := by
  have himg : Nat.divisors (m * n) = (Nat.divisors m ×ˢ Nat.divisors n).image
      (fun p : ℕ × ℕ => p.1 * p.2) := by
    rw [Nat.divisors_mul]
    exact Finset.mul_def
  unfold divChiNeg2Sum
  rw [himg, Finset.sum_image h.mul_injOn_divisors, Finset.sum_product,
    Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simpa using ZMod.χ₈'.map_mul (a : ZMod 8) (b : ZMod 8)

/-- `divChiNeg2Sum 1 = 1`. -/
public theorem divChiNeg2Sum_one : divChiNeg2Sum 1 = 1 := by
  rw [divChiNeg2Sum, Nat.divisors_one, Finset.sum_singleton]
  exact chiNeg2_one

/-- On powers of 2 only the divisor 1 contributes. -/
public theorem divChiNeg2Sum_prime_pow_two (e : ℕ) :
    divChiNeg2Sum (2 ^ e) = 1 := by
  rw [divChiNeg2Sum, Nat.divisors_prime_pow Nat.prime_two, Finset.sum_map, Function.Embedding.coeFn_mk]
  rw [Finset.sum_eq_single 0]
  · simp [ZMod.χ₈'_nat_eq_if_mod_eight]
  · intro j _ hj0
    obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    have hmod : (2 ^ (c + 1)) % 2 = 0 := by
      rw [Nat.pow_mod]
      norm_num
    rw [ZMod.χ₈'_nat_eq_if_mod_eight, if_pos hmod]
  · intro h
    simp at h

/-- Powers of 3 alternate between 1 and 3 mod 8. -/
private theorem pow_three_mod_eight (j : ℕ) :
    (3 ^ j) % 8 = if Even j then 1 else 3 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' j
  · rw [ite_eq_left (even_two_mul m), pow_mul, Nat.pow_mod]
    norm_num
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one m)), pow_succ, pow_mul,
      Nat.mul_mod, Nat.pow_mod]
    norm_num

/-- Powers of 5 alternate between 1 and 5 mod 8. -/
private theorem pow_five_mod_eight (j : ℕ) :
    (5 ^ j) % 8 = if Even j then 1 else 5 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' j
  · rw [ite_eq_left (even_two_mul m), pow_mul, Nat.pow_mod]
    norm_num
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one m)), pow_succ, pow_mul,
      Nat.mul_mod, Nat.pow_mod]
    norm_num

/-- Powers of 7 alternate between 1 and 7 mod 8. -/
private theorem pow_seven_mod_eight (j : ℕ) :
    (7 ^ j) % 8 = if Even j then 1 else 7 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' j
  · rw [ite_eq_left (even_two_mul m), pow_mul, Nat.pow_mod]
    norm_num
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one m)), pow_succ, pow_mul,
      Nat.mul_mod, Nat.pow_mod]
    norm_num

/-- On `p ^ e` with `p ≡ 1, 3 mod 8`, every divisor contributes 1. -/
public theorem divChiNeg2Sum_prime_pow_split {p e : ℕ} (hp : p.Prime)
    (h : p % 8 = 1 ∨ p % 8 = 3) :
    divChiNeg2Sum (p ^ e) = ((e + 1 : ℕ) : ℤ) := by
  have hpodd : Odd p := hp.odd_of_ne_two (by rcases h with h | h <;> omega)
  rw [divChiNeg2Sum, Nat.divisors_prime_pow hp, Finset.sum_map, Function.Embedding.coeFn_mk]
  have hall : ∀ j ∈ Finset.range (e + 1), ZMod.χ₈' (↑(p ^ j)) = 1 := by
    intro j _
    have hodd : Odd (p ^ j) := hpodd.pow
    have hm2 : (p ^ j) % 2 ≠ 0 := by
      rw [Nat.odd_iff] at hodd
      omega
    have hm8 : (p ^ j) % 8 = 1 ∨ (p ^ j) % 8 = 3 := by
      rcases h with h | h
      · rw [Nat.pow_mod, h]
        simp
      · rw [Nat.pow_mod, h, pow_three_mod_eight]
        by_cases hj : Even j <;> simp [hj]
    rw [ZMod.χ₈'_nat_eq_if_mod_eight, if_neg hm2, if_pos hm8]
  rw [Finset.sum_congr rfl hall]
  simp

/-- The alternating partial sums `Σ_{j ≤ f} (-1)^j`. -/
private theorem sum_neg_one_pow_range (f : ℕ) :
    ∑ j ∈ Finset.range (f + 1), (-1 : ℤ) ^ j
      = if Even f then 1 else 0 := by
  rw [neg_one_geom_sum]
  by_cases hf : Even f <;> simp [hf, Nat.even_add_one]

/-- On `q ^ f` with `q ≡ 5, 7 mod 8`, the divisor sum is 1 for even `f`
and 0 for odd `f`. -/
public theorem divChiNeg2Sum_prime_pow_inert {q f : ℕ} (hp : q.Prime)
    (h : q % 8 = 5 ∨ q % 8 = 7) :
    divChiNeg2Sum (q ^ f) = if Even f then 1 else 0 := by
  have hqodd : Odd q := hp.odd_of_ne_two (by rcases h with h | h <;> omega)
  rw [divChiNeg2Sum, Nat.divisors_prime_pow hp, Finset.sum_map, Function.Embedding.coeFn_mk]
  have hall : ∀ j ∈ Finset.range (f + 1), ZMod.χ₈' (↑(q ^ j)) = (-1 : ℤ) ^ j := by
    intro j _
    have hodd : Odd (q ^ j) := hqodd.pow
    have hm2 : (q ^ j) % 2 ≠ 0 := by
      rw [Nat.odd_iff] at hodd
      omega
    have hm8 : (q ^ j) % 8 = if Even j then 1 else q % 8 := by
      rcases h with h | h
      · rw [Nat.pow_mod, h, pow_five_mod_eight]
      · rw [Nat.pow_mod, h, pow_seven_mod_eight]
    by_cases hj : Even j
    · rw [if_pos hj] at hm8
      rw [ZMod.χ₈'_nat_eq_if_mod_eight, if_neg hm2,
        if_pos (Or.inl hm8), hj.neg_one_pow]
    · rw [if_neg hj] at hm8
      have hodd' : Odd j := by
        rcases Nat.even_or_odd j with h | h
        · exact absurd h hj
        · exact h
      rw [ZMod.χ₈'_nat_eq_if_mod_eight, if_neg hm2,
        if_neg (by rcases h with h | h <;> omega),
        hodd'.neg_one_pow]
  rw [Finset.sum_congr rfl hall]
  exact sum_neg_one_pow_range f

/-- Nonnegativity of the norm on `ℤ√(-2)`. -/
private theorem norm_nonneg (x : ℤ√(-2 : ℤ)) : 0 ≤ Zsqrtd.norm x :=
  Zsqrtd.norm_nonneg (by norm_num) x

/-- Elements of `ℤ[√-2]` with `natAbs`-norm equal to `t` form a finite type. -/
public noncomputable instance x2y2ReprFintype (t : ℕ) :
    Fintype {z : ℤ√(-2 : ℤ) // (Zsqrtd.norm z).natAbs = t} := by
  have hnn2 : (t : ℤ) ≤ (t : ℤ) * t := by
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · simp
    · have h1 : (1 : ℤ) ≤ t := by exact_mod_cast hpos
      have h := mul_le_mul_of_nonneg_right h1
        (show (0 : ℤ) ≤ (t : ℤ) by positivity)
      rwa [one_mul] at h
  have hbound : ∀ c : ℤ, c * c ≤ (t : ℤ) → |c| ≤ (t : ℤ) := by
    intro c hc
    have h2 : c ^ 2 ≤ (t : ℤ) ^ 2 := by
      rw [pow_two, pow_two]
      exact le_trans hc hnn2
    have h3 := sq_le_sq.mp h2
    rwa [abs_of_nonneg (show (0 : ℤ) ≤ (t : ℤ) by positivity)] at h3
  classical
  apply Fintype.ofInjective
    (fun a : {z : ℤ√(-2 : ℤ) // (Zsqrtd.norm z).natAbs = t} =>
      (⟨(a.1.re, a.1.im), by
        rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
        have hnn := norm_nonneg a.1
        have hnorm : Zsqrtd.norm a.1 = (t : ℤ) := by
          have h := Int.natAbs_of_nonneg hnn
          rw [a.2] at h
          exact h.symm
        rw [Zsqrtd.norm_def] at hnorm
        have hdecomp : a.1.re * a.1.re + 2 * (a.1.im * a.1.im) = (t : ℤ) := by
          linear_combination hnorm
        have him0 : 0 ≤ a.1.im * a.1.im := mul_self_nonneg _
        have hre0 : 0 ≤ a.1.re * a.1.re := mul_self_nonneg _
        have hre : a.1.re * a.1.re ≤ (t : ℤ) := by linarith
        have him : a.1.im * a.1.im ≤ (t : ℤ) := by linarith
        rw [← abs_le, ← abs_le]
        exact ⟨hbound _ hre, hbound _ him⟩⟩ :
        Finset.Icc (-(t : ℤ)) (t : ℤ) ×ˢ Finset.Icc (-(t : ℤ)) (t : ℤ)))
  intro a b hab
  have hpair : (a.1.re, a.1.im) = (b.1.re, b.1.im) := congrArg Subtype.val hab
  rw [Prod.mk.injEq] at hpair
  exact Subtype.ext (Zsqrtd.ext hpair.1 hpair.2)

/-- The representation count: elements of `ℤ[√-2]` of norm `t`. -/
public noncomputable def repX2Y2Count (t : ℕ) : ℕ :=
  Fintype.card {z : ℤ√(-2 : ℤ) // (Zsqrtd.norm z).natAbs = t}

/-- `repX2Y2Count 1 = 2`: the units. -/
public theorem repX2Y2Count_one : repX2Y2Count 1 = 2 :=
  Zsqrtd.card_repr_of_shape unitVal unitValInv unitVal_mul_unitValInv unitVal_inj
    unitVal_complete 1 (show (Zsqrtd.norm (1 : ℤ√(-2 : ℤ))).natAbs = 1 by decide)
    one_ne_zero (fun α hα => ⟨α, Zsqrtd.norm_eq_one_iff.mp hα, by simp⟩)

/-- `repX2Y2Count (2 ^ e) = 2`: ramified prime powers. -/
public theorem repX2Y2Count_two_pow (e : ℕ) : repX2Y2Count (2 ^ e) = 2 :=
  Zsqrtd.card_norm_two_pow (by norm_num) unitVal unitValInv unitVal_mul_unitValInv
    unitVal_inj unitVal_complete zsqrtd_neg_two_prime_sqrtd (by decide)
    ((zsqrtd_neg_two_isUnit_iff (-1)).mpr (Or.inr rfl)) (by decide) e

/-- Inert prime powers: 2 for even exponents, 0 for odd. -/
public theorem repX2Y2Count_inert_pow {q f : ℕ} [Fact q.Prime]
    (h : q % 8 = 5 ∨ q % 8 = 7) :
    repX2Y2Count (q ^ f) = if Even f then 2 else 0 :=
  Zsqrtd.card_norm_inert_pow (by norm_num) unitVal unitValInv unitVal_mul_unitValInv
    unitVal_inj unitVal_complete (zsqrtd_neg_two_inert h)

/-- `repX2Y2Count (p ^ e) = 2 * (e + 1)` for split `p`. -/
public theorem repX2Y2Count_split_pow {p e : ℕ} [Fact p.Prime]
    (h : p % 8 = 1 ∨ p % 8 = 3) {π : ℤ√(-2 : ℤ)}
    (hnorm : Zsqrtd.norm π = p) (hprime : Prime π) :
    repX2Y2Count (p ^ e) = 2 * (e + 1) := by
  have hconj3 := zsqrtd_neg_two_split_conj hnorm (by rcases h with h | h <;> omega)
  exact Zsqrtd.card_norm_split_pow (by norm_num) unitVal unitValInv unitVal_mul_unitValInv
    unitVal_inj unitVal_complete hnorm hprime hconj3.1 hconj3.2.1 hconj3.2.2

/-- On prime powers, elements of norm `p ^ e` number twice the divisor sum of `χ₋₂`. -/
private theorem repX2Y2Count_prime_pow {p e : ℕ} (hpprime : p.Prime) :
    (repX2Y2Count (p ^ e) : ℤ) = 2 * divChiNeg2Sum (p ^ e) := by
  have hfact : Fact p.Prime := ⟨hpprime⟩
  rcases hpprime.eq_two_or_odd with hp2 | hodd
  · rw [hp2, repX2Y2Count_two_pow, divChiNeg2Sum_prime_pow_two]
    norm_num
  have h8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rcases h8 with h8 | h8 | h8 | h8
  · obtain ⟨π, hnorm, hprime⟩ := zsqrtd_neg_two_split (Or.inl h8)
    rw [repX2Y2Count_split_pow (Or.inl h8) hnorm hprime,
      divChiNeg2Sum_prime_pow_split hpprime (Or.inl h8)]
    push_cast
    ring
  · obtain ⟨π, hnorm, hprime⟩ := zsqrtd_neg_two_split (Or.inr h8)
    rw [repX2Y2Count_split_pow (Or.inr h8) hnorm hprime,
      divChiNeg2Sum_prime_pow_split hpprime (Or.inr h8)]
    push_cast
    ring
  all_goals
    have h57 : p % 8 = 5 ∨ p % 8 = 7 := by omega
    rw [repX2Y2Count_inert_pow h57, divChiNeg2Sum_prime_pow_inert hpprime h57]
    by_cases he : Even e
    · rw [ite_eq_left he, ite_eq_left he]
      norm_num
    · rw [ite_eq_right he, ite_eq_right he]
      norm_num

/-- The `x ^ 2 + 2 * y ^ 2` representation count: representations of `t ≠ 0`
number twice the divisor sum of `χ₋₂`. -/
public theorem x2y2_count {t : ℕ} (ht : t ≠ 0) :
    (repX2Y2Count t : ℤ) = 2 * divChiNeg2Sum t := by
  have h := Zsqrtd.card_norm_eq_mul_of_prime_pow (by norm_num : (-2 : ℤ) < 0) unitVal
    unitValInv unitVal_mul_unitValInv unitVal_inj unitVal_complete divChiNeg2Sum_one
    divChiNeg2Sum_mul_of_coprime (fun hp _ => by exact_mod_cast repX2Y2Count_prime_pow hp) ht
  exact_mod_cast h

/-- The norm of a norm-fiber element, as an integer equation. -/
private theorem norm_eq_of_mem {N : ℕ} {z : ℤ√(-2 : ℤ)}
    (hz : (Zsqrtd.norm z).natAbs = N) : Zsqrtd.norm z = (N : ℤ) := by
  have hnn := Zsqrtd.norm_nonneg (show (-2 : ℤ) ≤ 0 by norm_num) z
  have h := Int.natAbs_of_nonneg hnn
  rw [hz] at h
  exact h.symm

/-- An element of `ℤ[√-2]` of norm `N` satisfies `re * re + 2 * (im * im) = N`. -/
public theorem re_mul_re_add_two_mul_im_mul_im {N : ℕ} {z : ℤ√(-2 : ℤ)}
    (hz : (Zsqrtd.norm z).natAbs = N) :
    z.re * z.re + 2 * (z.im * z.im) = (N : ℤ) := by
  have hnorm := norm_eq_of_mem hz
  rw [Zsqrtd.norm_def] at hnorm
  linear_combination hnorm

/-- The `natAbs` pair satisfies the norm equation over `ℕ`. -/
private theorem natAbs_sq_add {N : ℕ} {z : ℤ√(-2 : ℤ)}
    (hz : (Zsqrtd.norm z).natAbs = N) :
    z.re.natAbs ^ 2 + 2 * z.im.natAbs ^ 2 = N := by
  have hnorm := re_mul_re_add_two_mul_im_mul_im hz
  have hI : ((z.re.natAbs ^ 2 + 2 * z.im.natAbs ^ 2 : ℕ) : ℤ)
      = (N : ℤ) := by
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
    rw [Int.natAbs_sq z.re, Int.natAbs_sq z.im]
    have e1 : z.re * z.re = z.re ^ 2 := by ring
    have e2 : z.im * z.im = z.im ^ 2 := by ring
    omega
  exact_mod_cast hI

/-- The `natAbs` components are bounded by `N`. -/
private theorem natAbs_le_of_norm {N : ℕ} {z : ℤ√(-2 : ℤ)}
    (hz : (Zsqrtd.norm z).natAbs = N) :
    z.re.natAbs ≤ N ∧ z.im.natAbs ≤ N := by
  have heq := natAbs_sq_add hz
  have ha2 : z.re.natAbs ^ 2 ≤ N := by omega
  have hb2 : z.im.natAbs ^ 2 ≤ N := by omega
  constructor
  · exact le_trans (Nat.le_mul_self _) (by rw [← pow_two]; exact ha2)
  · exact le_trans (Nat.le_mul_self _) (by rw [← pow_two]; exact hb2)

/-- Squares ignore the sign encoding. -/
private theorem sq_if_sign (b : Bool) (a : ℤ) :
    (if b then a else -a) * (if b then a else -a) = a * a := by
  cases b <;> simp

/-- Sign recovery: `decide` inverts the sign encoding on positives. -/
private theorem decide_if_sign (b : Bool) (a : ℤ) (h : 0 < a) :
    decide (0 < (if b then a else -a)) = b := by
  cases b
  · change decide (0 < -a) = false
    have hneg : ¬(0 : ℤ) < -a := by omega
    have h1 : decide (0 < -a) ≠ true := by
      intro hcon
      rw [decide_eq_true_eq] at hcon
      exact hneg hcon
    exact eq_false_of_ne_true h1
  · change decide (0 < a) = true
    rw [decide_eq_true_eq]
    exact h

/-- `natAbs` ignores the sign encoding. -/
private theorem natAbs_if_sign (b : Bool) (n : ℕ) :
    (if b then (n : ℤ) else -(n : ℤ)).natAbs = n := by
  cases b <;> simp

/-- Norm of a signed pair is the unsigned norm. -/
private theorem norm_signed_pair (b₁ b₂ : Bool) (a c : ℤ) :
    Zsqrtd.norm (⟨(if b₁ then a else -a), (if b₂ then c else -c)⟩ :
      ℤ√(-2 : ℤ)) = a * a + 2 * (c * c) := by
  have e1 := sq_if_sign b₁ a
  have e2 := sq_if_sign b₂ c
  rw [Zsqrtd.norm_def]
  change (if b₁ then a else -a) * (if b₁ then a else -a)
      - (-2) * (if b₂ then c else -c) * (if b₂ then c else -c)
      = a * a + 2 * (c * c)
  linear_combination e1 + 2 * e2

/-- If no point of norm `N` in `ℤ[√-2]` has a zero coordinate, the number of
representations `x^2 + 2y^2 = N` is four times the number with `x, y > 0`. -/
public theorem repX2Y2Count_eq_four_mul_pos (N : ℕ)
    (hre : ∀ z : ℤ√(-2 : ℤ), (Zsqrtd.norm z).natAbs = N → z.re ≠ 0)
    (him : ∀ z : ℤ√(-2 : ℤ), (Zsqrtd.norm z).natAbs = N → z.im ≠ 0) :
    repX2Y2Count N = 4 * (((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
      (fun p : ℕ × ℕ => p.1 ^ 2 + 2 * p.2 ^ 2 = N ∧ 0 < p.1 ∧ 0 < p.2))).card := by
  set Pos : Finset (ℕ × ℕ) := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
    (fun p : ℕ × ℕ => p.1 ^ 2 + 2 * p.2 ^ 2 = N ∧ 0 < p.1 ∧ 0 < p.2)
    with hPos
  have hmem_to : ∀ z : {z : ℤ√(-2 : ℤ) // (Zsqrtd.norm z).natAbs = N},
      (z.1.re.natAbs, z.1.im.natAbs) ∈ Pos := by
    intro z
    have hre := hre z.1 z.2
    have him := him z.1 z.2
    have heq := natAbs_sq_add z.2
    have hle := natAbs_le_of_norm z.2
    have ha0 : 0 < z.1.re.natAbs := Int.natAbs_pos.mpr hre
    have hb0 : 0 < z.1.im.natAbs := Int.natAbs_pos.mpr him
    rw [hPos, Finset.mem_filter]
    constructor
    · rw [Finset.mem_product]
      constructor
      · rw [Finset.mem_Icc]
        change 1 ≤ z.1.re.natAbs ∧ z.1.re.natAbs ≤ N
        constructor <;> omega
      · rw [Finset.mem_Icc]
        change 1 ≤ z.1.im.natAbs ∧ z.1.im.natAbs ≤ N
        constructor <;> omega
    · change z.1.re.natAbs ^ 2 + 2 * z.1.im.natAbs ^ 2 = N ∧
        0 < z.1.re.natAbs ∧ 0 < z.1.im.natAbs
      exact ⟨heq, ha0, hb0⟩
  have hmem_of : ∀ b : Bool × Bool, ∀ p : ↥Pos,
      (Zsqrtd.norm (⟨(if b.1 then (p.1.1 : ℤ) else -(p.1.1 : ℤ)),
        (if b.2 then (p.1.2 : ℤ) else -(p.1.2 : ℤ))⟩ :
        ℤ√(-2 : ℤ))).natAbs = N := by
    intro b p
    have hmem' : p.1 ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
        (fun p : ℕ × ℕ => p.1 ^ 2 + 2 * p.2 ^ 2 = N ∧ 0 < p.1 ∧ 0 < p.2) := p.2
    rw [Finset.mem_filter] at hmem'
    obtain ⟨-, heq, ha0, hb0⟩ := hmem'
    have hnorm : Zsqrtd.norm (⟨(if b.1 then (p.1.1 : ℤ) else -(p.1.1 : ℤ)),
        (if b.2 then (p.1.2 : ℤ) else -(p.1.2 : ℤ))⟩ :
        ℤ√(-2 : ℤ)) = (N : ℤ) := by
      rw [norm_signed_pair]
      have h2 : ((p.1.1 ^ 2 + 2 * p.1.2 ^ 2 : ℕ) : ℤ) = (N : ℤ) := by
        exact_mod_cast heq
      push_cast at h2
      linear_combination h2
    rw [hnorm]
    exact Int.natAbs_natCast N
  have hequiv : {z : ℤ√(-2 : ℤ) // (Zsqrtd.norm z).natAbs = N}
      ≃ (Bool × Bool) × ↥Pos :=
    { toFun := fun z => ((decide (0 < z.1.re), decide (0 < z.1.im)),
        ⟨(z.1.re.natAbs, z.1.im.natAbs), hmem_to z⟩),
      invFun := fun t => ⟨⟨(if t.1.1 then (t.2.1.1 : ℤ) else -(t.2.1.1 : ℤ)),
        (if t.1.2 then (t.2.1.2 : ℤ) else -(t.2.1.2 : ℤ))⟩,
        hmem_of t.1 t.2⟩,
      right_inv := by
        rintro ⟨⟨b₁, b₂⟩, p, hmem⟩
        have hmem' := hmem
        rw [hPos, Finset.mem_filter] at hmem'
        obtain ⟨-, heq, ha0, hb0⟩ := hmem'
        have ha0I : (0:ℤ) < (p.1 : ℤ) := by exact_mod_cast ha0
        have hb0I : (0:ℤ) < (p.2 : ℤ) := by exact_mod_cast hb0
        have g1 := decide_if_sign b₁ (p.1 : ℤ) ha0I
        have g2 := decide_if_sign b₂ (p.2 : ℤ) hb0I
        have n1 := natAbs_if_sign b₁ p.1
        have n2 := natAbs_if_sign b₂ p.2
        apply Prod.ext
        · change (decide (0 < (if b₁ then (p.1 : ℤ) else -(p.1 : ℤ))),
            decide (0 < (if b₂ then (p.2 : ℤ) else -(p.2 : ℤ)))) = (b₁, b₂)
          rw [g1, g2]
        · apply Subtype.ext
          change ((if b₁ then (p.1 : ℤ) else -(p.1 : ℤ)).natAbs,
            (if b₂ then (p.2 : ℤ) else -(p.2 : ℤ)).natAbs) = p
          rw [n1, n2],
      left_inv := by
        rintro ⟨z, hz⟩
        apply Subtype.ext
        change (⟨(if decide (0 < z.re) then (z.re.natAbs : ℤ)
          else -(z.re.natAbs : ℤ)),
          (if decide (0 < z.im) then (z.im.natAbs : ℤ)
          else -(z.im.natAbs : ℤ))⟩ : ℤ√(-2 : ℤ)) = z
        apply Zsqrtd.ext
        · change (if decide (0 < z.re) then (z.re.natAbs : ℤ)
            else -(z.re.natAbs : ℤ)) = z.re
          by_cases h : 0 < z.re
          · have h1 : decide (0 < z.re) = true := by
              rw [decide_eq_true_eq]
              exact h
            rw [ite_eq_left h1]
            exact Int.natAbs_of_nonneg (le_of_lt h)
          · have hle : z.re ≤ 0 := by omega
            have h2 : decide (0 < z.re) ≠ true := by
              intro hcon
              rw [decide_eq_true_eq] at hcon
              exact h hcon
            rw [ite_eq_right h2]
            have e := Int.ofNat_natAbs_of_nonpos hle
            omega
        · change (if decide (0 < z.im) then (z.im.natAbs : ℤ)
            else -(z.im.natAbs : ℤ)) = z.im
          by_cases h : 0 < z.im
          · have h1 : decide (0 < z.im) = true := by
              rw [decide_eq_true_eq]
              exact h
            rw [ite_eq_left h1]
            exact Int.natAbs_of_nonneg (le_of_lt h)
          · have hle : z.im ≤ 0 := by omega
            have h2 : decide (0 < z.im) ≠ true := by
              intro hcon
              rw [decide_eq_true_eq] at hcon
              exact h hcon
            rw [ite_eq_right h2]
            have e := Int.ofNat_natAbs_of_nonpos hle
            omega }
  have hcard := Fintype.card_congr hequiv
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_coe] at hcard
  change Fintype.card {z : ℤ√(-2 : ℤ) // (Zsqrtd.norm z).natAbs = N}
    = 4 * Pos.card
  omega

/-- The `χ₋₂` divisor sum is unchanged by doubling an odd argument. -/
public theorem divChiNeg2Sum_two_mul_of_odd {m : ℕ} (hodd : Odd m) :
    divChiNeg2Sum (2 * m) = divChiNeg2Sum m := by
  have h2 := divChiNeg2Sum_prime_pow_two 1
  rw [pow_one] at h2
  rw [divChiNeg2Sum_mul_of_coprime (Nat.coprime_two_left.mpr hodd), h2, one_mul]

end

end SumSquares

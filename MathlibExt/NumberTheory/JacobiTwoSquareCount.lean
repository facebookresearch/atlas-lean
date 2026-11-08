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
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import MathlibExt.NumberTheory.GaussianIntPrimeBasics
public import MathlibExt.NumberTheory.GaussianIntSplitPrimes
public import MathlibExt.NumberTheory.SumSquares.RepresentationCount
public import MathlibExt.NumberTheory.ZsqrtdNormFactorization
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Jacobi two-square count formula

The number `SumSquares.representationNumber 2 n` of ordered signed representations of `n`
as a sum of two squares equals four times the divisor sum of the nonprincipal character mod 4
(`representationNumber_two_jacobi_count`). The proof counts Gaussian integers of norm `n`
with the ring-independent norm-fiber counts of `MathlibExt.NumberTheory.ZsqrtdNormFactorization`
at `d = -1`.

## References

Jacobi's two-square theorem `r₂(n) = 4 (d₁(n) - d₃(n))`: G. H. Hardy and E. M. Wright,
*An Introduction to the Theory of Numbers*, 6th edition, Oxford University Press, 2008,
Section 16.9, Theorem 278.
The proof develops the Gaussian-integer route directly (norm multiplicativity and prime
splitting in `ℤ[i]`, from the `GaussianInt` lemmas in `GaussianIntPrimeBasics` and
`GaussianIntSplitPrimes`, plus divisor bookkeeping). It does not adapt the separate Gaussian
norm-count development in `MathlibExt/NumberTheory/ArithmeticFunction/FourTriangularNumbers.lean`,
which is the related existing repository development for Gaussian norm counts.
-/

local notation "ℤ[i]" => GaussianInt

namespace SumSquares

open GaussianInt (gaussianInt_prime_one_add_I gaussianInt_two_eq gaussianInt_split_prime
  gaussianIntReprFintype gaussianInt_card_repr_prime_pow unitVal unitValInv
  unitVal_mul_unitValInv unitVal_inj unitVal_complete)

@[expose] public section

/-- The divisor sum of `χ`. -/
public noncomputable def divChiSum (n : ℕ) : ℤ := ∑ d ∈ Nat.divisors n, ZMod.χ₄ d

/-- Divisor sums of a completely multiplicative function are multiplicative. -/
public theorem divChiSum_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    divChiSum (m * n) = divChiSum m * divChiSum n := by
  have himg : Nat.divisors (m * n) = (Nat.divisors m ×ˢ Nat.divisors n).image
      (fun p : ℕ × ℕ => p.1 * p.2) := by
    rw [Nat.divisors_mul]
    exact Finset.mul_def
  unfold divChiSum
  rw [himg, Finset.sum_image h.mul_injOn_divisors, Finset.sum_product,
    Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simpa using ZMod.χ₄.map_mul (a : ZMod 4) (b : ZMod 4)

/-- `divChiSum 1 = 1`. -/
public theorem divChiSum_one : divChiSum 1 = 1 := by
  simp [divChiSum]

/-- On powers of 2 only the divisor 1 contributes. -/
public theorem divChiSum_prime_pow_two (e : ℕ) : divChiSum (2 ^ e) = 1 := by
  rw [divChiSum, Nat.divisors_prime_pow Nat.prime_two, Finset.sum_map, Function.Embedding.coeFn_mk]
  rw [Finset.sum_eq_single 0]
  · simp [ZMod.χ₄_nat_eq_if_mod_four]
  · intro j _ hj0
    obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    have hmod : (2 ^ (c + 1)) % 2 = 0 := by
      rw [Nat.pow_mod]
      norm_num
    rw [ZMod.χ₄_nat_eq_if_mod_four, if_pos hmod]
  · intro h
    simp at h

/-- `p ^ j ≡ 1 mod 4` when `p ≡ 1 mod 4`. -/
private theorem pow_mod_four_eq_one_of {p j : ℕ} (h : p % 4 = 1) :
    (p ^ j) % 4 = 1 := by
  rw [Nat.pow_mod, h]
  simp

/-- On `p ^ e` with `p ≡ 1 mod 4`, every divisor contributes 1. -/
public theorem divChiSum_prime_pow_split {p e : ℕ} (hp : p.Prime)
    (h : p % 4 = 1) : divChiSum (p ^ e) = ((e + 1 : ℕ) : ℤ) := by
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  rw [divChiSum, Nat.divisors_prime_pow hp, Finset.sum_map, Function.Embedding.coeFn_mk]
  have hall : ∀ j ∈ Finset.range (e + 1), ZMod.χ₄ (↑(p ^ j)) = 1 := by
    intro j _
    have hodd : Odd (p ^ j) := hpodd.pow
    have hm2 : (p ^ j) % 2 ≠ 0 := by
      rw [Nat.odd_iff] at hodd
      omega
    have hm4 : (p ^ j) % 4 = 1 := pow_mod_four_eq_one_of h
    rw [ZMod.χ₄_nat_eq_if_mod_four, if_neg hm2, if_pos hm4]
  rw [Finset.sum_congr rfl hall]
  simp

/-- Powers of 3 alternate between 1 and 3 mod 4. -/
private theorem pow_three_mod_four (j : ℕ) :
    (3 ^ j) % 4 = if Even j then 1 else 3 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' j
  · rw [ite_eq_left (even_two_mul m), pow_mul, Nat.pow_mod]
    norm_num
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one m)), pow_succ, pow_mul,
      Nat.mul_mod, Nat.pow_mod]
    norm_num

/-- The alternating partial sums `Σ_{j ≤ f} (-1)^j`. -/
private theorem sum_neg_one_pow_range (f : ℕ) :
    ∑ j ∈ Finset.range (f + 1), (-1 : ℤ) ^ j
      = if Even f then 1 else 0 := by
  rw [neg_one_geom_sum]
  by_cases hf : Even f <;> simp [hf, Nat.even_add_one]

/-- On `q ^ f` with `q ≡ 3 mod 4`, the divisor sum is 1 for even `f`
and 0 for odd `f`. -/
public theorem divChiSum_prime_pow_inert {q f : ℕ} (hp : q.Prime)
    (h : q % 4 = 3) : divChiSum (q ^ f) = if Even f then 1 else 0 := by
  have hqodd : Odd q := hp.odd_of_ne_two (by omega)
  rw [divChiSum, Nat.divisors_prime_pow hp, Finset.sum_map, Function.Embedding.coeFn_mk]
  have hall : ∀ j ∈ Finset.range (f + 1), ZMod.χ₄ (↑(q ^ j)) = (-1 : ℤ) ^ j := by
    intro j _
    have hodd : Odd (q ^ j) := hqodd.pow
    have hm2 : (q ^ j) % 2 ≠ 0 := by
      rw [Nat.odd_iff] at hodd
      omega
    have hm4 : (q ^ j) % 4 = (3 ^ j) % 4 := by
      rw [Nat.pow_mod, Nat.pow_mod, h]
    rw [pow_three_mod_four] at hm4
    by_cases hj : Even j
    · rw [if_pos hj] at hm4
      rw [ZMod.χ₄_nat_eq_if_mod_four, if_neg hm2, if_pos hm4, hj.neg_one_pow]
    · rw [if_neg hj] at hm4
      have hodd' : Odd j := by
        rcases Nat.even_or_odd j with h | h
        · exact absurd h hj
        · exact h
      rw [ZMod.χ₄_nat_eq_if_mod_four, if_neg hm2,
        if_neg (by omega : (q ^ j) % 4 ≠ 1)]
      rw [hodd'.neg_one_pow]
  rw [Finset.sum_congr rfl hall]
  exact sum_neg_one_pow_range f

/-- The representation count: Gaussian integers of norm `n`. -/
private noncomputable def repCount (n : ℕ) : ℕ :=
  Fintype.card {α : ℤ[i] // (Zsqrtd.norm α).natAbs = n}

/-- The unit in the factorization `2 = -i * (1 + i)^2`. -/
private def ramUnit : ℤ[i]ˣ := ⟨⟨0, -1⟩, ⟨0, 1⟩, by decide, by decide⟩

/-- On prime powers, Gaussian integers of norm `p ^ e` number four times the divisor sum. -/
private theorem repCount_prime_pow {p e : ℕ} (hpprime : p.Prime) :
    (repCount (p ^ e) : ℤ) = 4 * divChiSum (p ^ e) := by
  have hfact : Fact p.Prime := ⟨hpprime⟩
  have h4 : p % 4 = 0 ∨ p % 4 = 1 ∨ p % 4 = 2 ∨ p % 4 = 3 := by omega
  rcases h4 with h4 | h4 | h4 | h4
  · have hp2 : p = 2 := by
      rcases hpprime.eq_two_or_odd with h | h
      · exact h
      · exfalso
        omega
    rw [hp2, repCount, Zsqrtd.card_norm_two_pow (by norm_num) unitVal unitValInv
      unitVal_mul_unitValInv unitVal_inj unitVal_complete gaussianInt_prime_one_add_I
      (by decide) ramUnit.isUnit gaussianInt_two_eq, divChiSum_prime_pow_two]
    norm_num
  · obtain ⟨π, hnorm, hprime⟩ := gaussianInt_split_prime h4
    rw [repCount, gaussianInt_card_repr_prime_pow h4 hnorm hprime,
      divChiSum_prime_pow_split hpprime h4]
    push_cast
    ring
  · have hp2 : p = 2 := by
      rcases hpprime.eq_two_or_odd with h | h
      · exact h
      · exfalso
        omega
    rw [hp2, repCount, Zsqrtd.card_norm_two_pow (by norm_num) unitVal unitValInv
      unitVal_mul_unitValInv unitVal_inj unitVal_complete gaussianInt_prime_one_add_I
      (by decide) ramUnit.isUnit gaussianInt_two_eq, divChiSum_prime_pow_two]
    norm_num
  · rw [repCount, Zsqrtd.card_norm_inert_pow (by norm_num) unitVal unitValInv
      unitVal_mul_unitValInv unitVal_inj unitVal_complete
      ((GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p).mpr h4),
      divChiSum_prime_pow_inert hpprime h4]
    by_cases he : Even e
    · rw [ite_eq_left he, ite_eq_left he]
      norm_num
    · rw [ite_eq_right he, ite_eq_right he]
      norm_num

/-- The Jacobi two-square count formula: representations of `n ≠ 0` as a
sum of two squares number four times the divisor sum of `χ`. -/
private theorem jacobi_two_square_count {n : ℕ} (hn : n ≠ 0) :
    (repCount n : ℤ) = 4 * divChiSum n := by
  have h := Zsqrtd.card_norm_eq_mul_of_prime_pow (by norm_num : (-1 : ℤ) < 0) unitVal
    unitValInv unitVal_mul_unitValInv unitVal_inj unitVal_complete divChiSum_one
    divChiSum_mul_of_coprime (fun hp _ => by exact_mod_cast repCount_prime_pow hp) hn
  exact_mod_cast h

/-- Integer pairs representing `j` as a sum of two squares correspond to
Gaussian integers of norm `j`. -/
public def pairEquivGaussianNormFiber (j : ℕ) :
    {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = (j : ℤ)} ≃
      {z : ℤ[i] // (Zsqrtd.norm z).natAbs = j} where
  toFun p := ⟨⟨p.1.1, p.1.2⟩, by
    have hnorm : Zsqrtd.norm (⟨p.1.1, p.1.2⟩ : ℤ[i]) =
        p.1.1 ^ 2 + p.1.2 ^ 2 := by
      rw [Zsqrtd.norm_def]
      dsimp only
      ring
    rw [hnorm, p.2, Int.natAbs_natCast]⟩
  invFun z := ⟨(z.1.re, z.1.im), by
    have hnonneg : 0 ≤ Zsqrtd.norm z.1 := GaussianInt.norm_nonneg z.1
    have hnorm : Zsqrtd.norm z.1 = (j : ℤ) := by
      rw [← Int.natAbs_of_nonneg hnonneg, z.2]
    rw [Zsqrtd.norm_def] at hnorm
    simpa [pow_two] using hnorm⟩
  left_inv p := Subtype.ext rfl
  right_inv z := Subtype.ext rfl

noncomputable instance pairSquareFintype (j : ℕ) :
    Fintype {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = (j : ℤ)} :=
  Fintype.ofEquiv _ (pairEquivGaussianNormFiber j).symm

/-- The canonical two-square representation number
(`SumSquares.representationNumber 2 j`, ordered signed representations
by `Fin 2 → ℤ` vectors) counts the same representations as the
Gaussian-norm fiber: expanding `dotProduct` over `Fin 2` and using
`Fin 2 → ℤ ≃ ℤ × ℤ` identifies both counts. -/
public theorem representationNumber_two_eq (j : ℕ) :
    SumSquares.representationNumber 2 j =
      Fintype.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = (j : ℤ)} := by
  have e : {x : Fin 2 → ℤ // x ∈ SumSquares.solutions 2 j} ≃
      {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = (j : ℤ)} :=
    { toFun := fun x => ⟨(x.1 0, x.1 1), by
        simpa only [SumSquares.mem_solutions, dotProduct, Fin.sum_univ_two,
          pow_two] using x.2⟩,
      invFun := fun p => ⟨![p.1.1, p.1.2], by
        simpa only [SumSquares.mem_solutions, dotProduct, Fin.sum_univ_two,
          pow_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons] using p.2⟩,
      left_inv := fun x => by
        apply Subtype.ext
        funext i
        fin_cases i <;> rfl,
      right_inv := fun p => Subtype.ext rfl }
  unfold SumSquares.representationNumber
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_eq_fintype_card]

/-- Jacobi's two-square theorem, stated with the canonical
representation number: the number of ordered signed representations
of `j ≥ 1` as a sum of two squares equals four times the divisor sum
of `ZMod.χ₄`. Proved by bridging `SumSquares.representationNumber 2 j`
to the Gaussian-norm fiber count. -/
public theorem representationNumber_two_jacobi_count (j : ℕ) (hj : 1 ≤ j) :
    (SumSquares.representationNumber 2 j : ℤ) =
      4 * ∑ d ∈ j.divisors, ZMod.χ₄ d := by
  rw [representationNumber_two_eq,
    Fintype.card_congr (pairEquivGaussianNormFiber j)]
  simpa [repCount, divChiSum] using jacobi_two_square_count (n := j) (by omega)

end

end SumSquares

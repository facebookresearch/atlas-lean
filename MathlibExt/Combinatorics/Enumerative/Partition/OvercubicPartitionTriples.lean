/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Instances.ZMod
import MathlibExt.NumberTheory.DivisorCountParity
import MathlibExt.NumberTheory.SquareModEight

/-!
# Congruences for overcubic partition triples

The Euler product for the overcubic partition triple count gives a divisor-count formula
modulo four. It implies the congruences at multiples of sixteen of Nayaka, Dharmendra,
and Mahesh Kumar.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

local notation "𝔣" => qEulerProduct

/-- **The overcubic partition triple series.** The generating function of overcubic partition
triples is the integer power series $f_4^3 / (f_1^6 f_2^3)$ in $q$, where
$f_k = \prod_{j \ge 1} (1 - q^{kj})$; the inverse of $f_1^6 f_2^3$ exists because its constant
coefficient is $1$.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Section 1; the
same generating function is quoted from this paper by Saikia and Sarma (arXiv:2411.00013,
eq. (2)) and by Chen, Jin, and Yao (arXiv:2504.06941, eq. (1.1)). -/
noncomputable def overcubicTripleSeries : ℤ⟦X⟧ :=
  𝔣 4 ^ 3 * invOfUnit (𝔣 1 ^ 6 * 𝔣 2 ^ 3) 1

/-- **Number of overcubic partition triples.** For a natural number $n$, $\mathrm{bt}(n)$, the
number of overcubic partition triples of $n$, is defined as the integer coefficient of $q^n$ in
the power series $f_4^3 / (f_1^6 f_2^3)$, where $f_k = \prod_{j \ge 1} (1 - q^{kj})$.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Section 1. -/
noncomputable def overcubicTripleCount (n : ℕ) : ℤ :=
  coeff n overcubicTripleSeries

/-- **Generating function for overcubic partition triples.** For $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$, and let $\mathrm{bt}(n)$, the number of overcubic partition
triples of $n$, be the coefficient of $q^n$ in $f_4^3/(f_1^6 f_2^3)$. Then, as integer power
series in $q$,
$$f_1^6 f_2^3 \sum_{n \ge 0} \mathrm{bt}(n) q^n = f_4^3.$$

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Section 1. -/
theorem overcubicTripleCount_generatingFunction :
    𝔣 1 ^ 6 * 𝔣 2 ^ 3 * PowerSeries.mk overcubicTripleCount = 𝔣 4 ^ 3 := by
  have hmk : PowerSeries.mk overcubicTripleCount = overcubicTripleSeries := by
    ext n
    simp [overcubicTripleCount]
  have hc : constantCoeff (𝔣 1 ^ 6 * 𝔣 2 ^ 3) = ((1 : ℤˣ) : ℤ) := by
    simp [constantCoeff_qEulerProduct (le_refl 1),
      constantCoeff_qEulerProduct (by norm_num : 1 ≤ 2)]
  rw [hmk, overcubicTripleSeries, mul_left_comm, mul_invOfUnit _ _ hc, mul_one]

/-- **Overcubic partition triples of $0$.** The number $\mathrm{bt}(0)$ of overcubic partition
triples of $0$ equals $1$.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Section 1. -/
theorem overcubicTripleCount_zero : overcubicTripleCount 0 = 1 := by
  have h := congrArg (coeff 0) overcubicTripleCount_generatingFunction
  simp only [coeff_zero_eq_constantCoeff, map_mul, map_pow,
    constantCoeff_qEulerProduct (le_refl 1), constantCoeff_qEulerProduct (by norm_num : 1 ≤ 2),
    constantCoeff_qEulerProduct (by norm_num : 1 ≤ 4), one_pow, one_mul] at h
  simpa using h

namespace overcubicTripleCount_congruences_sixteen_mul_args

local notation "S" => (ZMod 4)⟦X⟧
local notation "reduce" => map (Int.castRingHom (ZMod 4))

/-- The positive multiples of a part size, each with weight one. -/
private noncomputable def multiples (d : ℕ) : S :=
  mk fun n => if d ∈ n.divisors then 1 else 0

private noncomputable def divisorSeries : S := mk fun n => (n.divisors.card : ZMod 4)

private lemma hasSum_multiples :
    HasSum (fun i => multiples (i + 1)) divisorSeries := by
  rw [hasSum_nat_add_iff 1]
  have hzero : multiples 0 = 0 := by
    ext n
    simp [multiples]
  simp only [Finset.sum_range_one, hzero, add_zero]
  apply (WithPiTopology.hasSum_iff_hasSum_coeff _).2
  intro n
  simp only [multiples, divisorSeries, coeff_mk]
  have h := hasSum_sum_of_ne_finset_zero (L := .unconditional ℕ) (s := n.divisors)
    (f := fun d => if d ∈ n.divisors then (1 : ZMod 4) else 0) (fun d hd => ite_eq_right hd)
  simpa only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul,
    mul_one] using h

private lemma geometric_factor {d : ℕ} (hd : 0 < d) :
    (1 - X ^ d) * multiples d = (X : S) ^ d := by
  rw [sub_mul, one_mul]
  ext n
  rw [map_sub, coeff_X_pow_mul', coeff_X_pow]
  obtain h | rfl | h := lt_trichotomy n d
  · have hmem : d ∉ n.divisors := fun hn => h.not_ge (Nat.divisor_le hn)
    simp only [multiples, coeff_mk, ite_eq_right hmem, ite_eq_right h.not_ge, sub_zero,
      ite_eq_right h.ne]
  · simp [multiples, hd.ne']
  · have hdiv : d ∣ n - d ↔ d ∣ n := Nat.dvd_sub_iff_left h.le (dvd_refl d)
    simp [multiples, h.le, Nat.mem_divisors, hdiv, Nat.sub_ne_zero_of_lt h,
      (hd.trans h).ne', h.ne']

private lemma four_zero : (4 : S) = 0 := by
  simpa only [map_ofNat, map_zero] using
    congrArg (C (R := ZMod 4)) (show (4 : ZMod 4) = 0 by decide)

private lemma mul_linear (a b : S) :
    (1 + 2 * a) * (1 + 2 * b) = 1 + 2 * (a + b) := by
  linear_combination (a * b) * four_zero

private lemma hasProd_linear {f : ℕ → S} {s : S} (h : HasSum f s) :
    HasProd (fun i => 1 + 2 * f i) (1 + 2 * s) := by
  have hprod (t : Finset ℕ) : ∏ i ∈ t, (1 + 2 * f i) = 1 + 2 * ∑ i ∈ t, f i := by
    induction t using Finset.induction_on with
    | empty => simp
    | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, mul_linear]
  simpa only [HasProd, hprod] using (Filter.Tendsto.const_add 1 (h.const_mul 2))

private lemma hasProd_euler (k : ℕ) (hk : 0 < k) :
    HasProd (fun i : ℕ => (1 : S) - X ^ (k * (i + 1))) (reduce (𝔣 k)) := by
  have hp : Multipliable fun i : ℕ => (1 : ℤ⟦X⟧) - X ^ (k * (i + 1)) := by
    simp_rw [sub_eq_add_neg]
    apply WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
    simp only [order_neg, order_X_pow]
    exact ENat.tendsto_natCast_nhds_top.comp <| Filter.tendsto_atTop_mono
      (fun i => Nat.le_mul_of_pos_left (i + 1) hk) (Filter.tendsto_add_atTop_nat 1)
  have hc : Continuous reduce :=
    continuous_pi fun d => (continuous_of_discreteTopology (f := fun z : ℤ => (z : ZMod 4))).comp
      (continuous_apply d)
  simpa [Function.comp_def, qEulerProduct] using hp.hasProd.map reduce hc

private lemma double_factor (x g : S) (hg : (1 - x) * g = x) :
    1 - x ^ 2 = (1 - x) ^ 2 * (1 + 2 * g) := by
  linear_combination -2 * (1 - x) * hg

/-- Modulo four the quotient of the doubled Euler product by the square of the original
product is linear in the series counting divisors. -/
private lemma euler_double (k : ℕ) (hk : 0 < k) :
    reduce (𝔣 k) ^ 2 * (1 + 2 * expand k hk.ne' divisorSeries) = reduce (𝔣 (2 * k)) := by
  have hs : HasSum (fun i => expand k hk.ne' (multiples (i + 1)))
      (expand k hk.ne' divisorSeries) := by
    apply (WithPiTopology.hasSum_iff_hasSum_coeff _).2
    intro n
    by_cases h : k ∣ n
    · simpa only [coeff_expand, ite_eq_left h] using
        ((WithPiTopology.hasSum_iff_hasSum_coeff _).1 hasSum_multiples) (n / k)
    · simp [coeff_expand, h]
  apply HasProd.unique _ (hasProd_euler (2 * k) (by omega))
  apply (((hasProd_euler k hk).pow 2).mul (hasProd_linear hs)).congr_fun
  intro i
  have hf := congrArg (expand k hk.ne') (geometric_factor (Nat.succ_pos i))
  simp only [map_mul, map_sub, map_one, map_pow, expand_X, ← pow_mul] at hf
  rw [show 2 * k * (i + 1) = k * (i + 1) * 2 by ring, pow_mul]
  exact double_factor _ _ hf

private lemma combine_factors (x y z a b : S)
    (h₁ : x ^ 2 * (1 + 2 * a) = y) (h₂ : y ^ 2 * (1 + 2 * b) = z) :
    (x ^ 6 * y ^ 3) * (1 + 2 * (a + b)) = z ^ 3 := by
  have h : (x ^ 2 * y) * ((1 + 2 * a) * (1 + 2 * b)) = z := by
    calc
      _ = (x ^ 2 * (1 + 2 * a)) * y * (1 + 2 * b) := by ring
      _ = z := by rw [h₁, ← sq, h₂]
  have hcube (s : S) : (1 + 2 * s) ^ 3 = 1 + 2 * s := by
    linear_combination (s + 3 * s ^ 2 + 2 * s ^ 3) * four_zero
  rw [← h, mul_pow, mul_linear, hcube, mul_pow, ← pow_mul]

private lemma series_mod_four :
    reduce overcubicTripleSeries =
      1 + 2 * (divisorSeries + expand 2 two_ne_zero divisorSeries) := by
  have h₁ : reduce (𝔣 1) ^ 2 * (1 + 2 * divisorSeries) = reduce (𝔣 2) := by
    simpa only [expand_one_apply, Nat.reduceMul] using euler_double 1 (by decide)
  have h₂ := euler_double 2 (by decide)
  have hu : IsUnit (𝔣 1 ^ 6 * 𝔣 2 ^ 3) := by
    rw [isUnit_iff_constantCoeff]
    simp [constantCoeff_qEulerProduct (by decide : 1 ≤ 1),
      constantCoeff_qEulerProduct (by decide : 1 ≤ 2)]
  have hmk : mk overcubicTripleCount = overcubicTripleSeries := by
    ext n
    simp [overcubicTripleCount]
  have hg := overcubicTripleCount_generatingFunction
  rw [hmk] at hg
  apply (hu.map reduce).mul_left_cancel
  rw [← map_mul, hg, map_pow, map_mul, map_pow, map_pow]
  exact (combine_factors _ _ _ _ _ h₁ h₂).symm

private lemma count_even (m : ℕ) (hm : 0 < m) :
    overcubicTripleCount (2 * m) ≡
      2 * ((2 * m).divisors.card + (m.divisors.card : ℤ)) [ZMOD 4] := by
  apply (ZMod.intCast_eq_intCast_iff _ _ 4).mp
  have h := congrArg (coeff (2 * m)) series_mod_four
  simpa [overcubicTripleCount, divisorSeries, coeff_one, hm.ne'] using h

/-- Removing powers of two leaves twice the divisor count of the odd part modulo four. -/
private lemma count_odd_part (t u : ℕ) (hu : Odd u) :
    overcubicTripleCount (2 ^ (t + 1) * u) ≡ 2 * (u.divisors.card : ℤ) [ZMOD 4] := by
  have hd (j : ℕ) : (2 ^ j * u).divisors.card = (j + 1) * u.divisors.card := by
    rw [Nat.Coprime.card_divisors_mul ((Nat.coprime_two_left.mpr hu).pow_left _),
      Nat.divisors_prime_pow Nat.prime_two, Finset.card_map, Finset.card_range]
  have hpos : 0 < u := by
    obtain ⟨v, rfl⟩ := hu
    omega
  have hm := count_even (2 ^ t * u) (Nat.mul_pos (pow_pos (by decide) _) hpos)
  rw [show 2 * (2 ^ t * u) = 2 ^ (t + 1) * u by ring] at hm
  apply hm.trans
  rw [hd, hd, Int.modEq_iff_dvd]
  refine ⟨-((t : ℤ) + 1) * u.divisors.card, ?_⟩
  push_cast
  ring

private lemma count_zero (t u : ℕ) (hu : Odd u) (hr : u % 8 ≠ 1) :
    overcubicTripleCount (2 ^ (t + 1) * u) ≡ 0 [ZMOD 4] := by
  have hns : ¬ IsSquare u := by
    rintro ⟨r, rfl⟩
    have h := Nat.sq_mod_eight r
    rw [sq] at h
    rw [Nat.odd_iff] at hu
    omega
  obtain ⟨v, hv⟩ := Nat.even_card_divisors_of_not_isSquare hns
  apply (count_odd_part t u hu).trans
  rw [hv, Nat.cast_add, Int.ModEq]
  omega

end overcubicTripleCount_congruences_sixteen_mul_args

open overcubicTripleCount_congruences_sixteen_mul_args in
/-- **Congruences for overcubic partition triples at multiples of 16.** Let $\mathrm{bt}(n)$ be the
number of overcubic partition triples of $n$. For all natural numbers $n$ and $\alpha$, each of
$\mathrm{bt}(64n+48)$, $\mathrm{bt}(128n+80)$, $\mathrm{bt}(128n+96)$, $\mathrm{bt}(256n+160)$ and
$\mathrm{bt}(256 \cdot 2^{\alpha} n + 192)$ is divisible by $4$, and
$\mathrm{bt}(256n+32) \equiv \mathrm{bt}(128n+16) \pmod 4$.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Theorem 11,
eqs. (33)-(38) (`integers-2024-A80-thm-11`). -/
theorem overcubicTripleCount_congruences_sixteen_mul_args (n α : ℕ) :
    overcubicTripleCount (64 * n + 48) ≡ 0 [ZMOD 4] ∧
      overcubicTripleCount (128 * n + 80) ≡ 0 [ZMOD 4] ∧
      overcubicTripleCount (128 * n + 96) ≡ 0 [ZMOD 4] ∧
      overcubicTripleCount (256 * n + 160) ≡ 0 [ZMOD 4] ∧
      overcubicTripleCount (256 * n + 32) ≡ overcubicTripleCount (128 * n + 16) [ZMOD 4] ∧
      overcubicTripleCount (256 * 2 ^ α * n + 192) ≡ 0 [ZMOD 4] := by
  have h₃ (m : ℕ) : Odd (4 * m + 3) := ⟨2 * m + 1, by ring⟩
  have h₅ : Odd (8 * n + 5) := ⟨4 * n + 2, by ring⟩
  have h₁ : Odd (8 * n + 1) := ⟨4 * n, by ring⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert count_zero 3 _ (h₃ n) (by omega) using 2
    ring
  · convert count_zero 3 _ h₅ (by omega) using 2
    ring
  · convert count_zero 4 _ (h₃ n) (by omega) using 2
    ring
  · convert count_zero 4 _ h₅ (by omega) using 2
    ring
  · convert (count_odd_part 4 _ h₁).trans (count_odd_part 3 _ h₁).symm using 2 <;> ring
  · convert count_zero 5 _ (h₃ (2 ^ α * n)) (by omega) using 2
    ring

end

end MetaMathlibExt

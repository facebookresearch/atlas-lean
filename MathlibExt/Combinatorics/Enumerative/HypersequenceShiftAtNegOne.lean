/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.AlternatingBinomialPowerSumRecurrences
public import MathlibExt.Combinatorics.Enumerative.HypersequenceMatrixB
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.AlternatingBinomialPowerSumStirling

/-!
# Parisse's hypersequence coefficients as shifts from −1

For integer parameters, the elementary symmetric entries (for degrees `k ≤ j`) and the entries
of Parisse's matrices `B` and `C` (for all natural row and column indices) can be recovered from
those at `-1`. For the first two identities, translating the product of the row's linear factors
by `n + 1` gives the binomial coefficients in its Taylor expansion. The degree restriction in the
first identity keeps the upper binomial index in the natural numbers. The third identity uses the
Stirling expansion of the alternating binomial power sum at shifts `n + 1` and `0`.

## References

* Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums II*,
  INTEGERS 26 (2026), Article A36, pp. 1–15, Proposition 3, Equations (3.20)–(3.22).
* Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
  INTEGERS 24 (2024), Article A70, pp. 1–31, Proposition 1(i), Equation (3.10), and
  Proposition 2(iii), for the Stirling expansions used in (3.22).
* Khristo N. Boyadzhiev, *Close Encounters with the Stirling Numbers of the Second Kind*,
  Mathematics Magazine 85 (2012), no. 4, pp. 252–266, p. 253 (the expansion in (3.10)).
* Ronald L. Graham, Donald E. Knuth, and Oren Patashnik, *Concrete Mathematics: A Foundation
  for Computer Science*, 2nd ed., Addison-Wesley, 1994, Identity (6.19) (the zero-shift value).
* The Taylor/Hasse coefficient extraction adapts `mitrinovicR_eq_sum_mitrinovicR_zero`
  (`MathlibExt/Combinatorics/Enumerative/MitrinovicNumbers.lean`, lines 127–141).
-/

namespace MetaMathlibExt

open Finset Polynomial

private noncomputable def rowPolynomial (n : ℤ) (j : ℕ) : ℤ[X] :=
  ∏ i ∈ Icc 1 j, (X + C (n + (i : ℤ)))

private theorem natDegree_rowPolynomial (n : ℤ) (j : ℕ) : (rowPolynomial n j).natDegree = j := by
  simpa [rowPolynomial, sub_eq_add_neg] using
    natDegree_finsetProd_X_sub_C_eq_card (Icc 1 j) (fun i : ℕ => -(n + (i : ℤ)))

private theorem coeff_rowPolynomial_shift (n : ℤ) (j d : ℕ) :
    (rowPolynomial n j).coeff d =
      ∑ i ∈ range (j - d + 1), ((d + i).choose d : ℤ) *
        (rowPolynomial (-1) j).coeff (d + i) * (n + 1) ^ i := by
  have hshift : rowPolynomial n j = taylor (n + 1) (rowPolynomial (-1) j) := by
    change (∏ i ∈ Icc 1 j, (X + C (n + (i : ℤ)))) =
      taylorAlgHom (n + 1) (∏ i ∈ Icc 1 j, (X + C (-1 + (i : ℤ))))
    rw [map_prod]
    refine prod_congr rfl fun i _ => ?_
    change X + C (n + (i : ℤ)) = taylor (n + 1) (X + C (-1 + (i : ℤ)))
    rw [map_add (taylor (n + 1)), taylor_X, taylor_C, add_assoc, ← C_add]
    congr 2
    ring
  have hdeg : (hasseDeriv d (rowPolynomial (-1) j)).natDegree < j - d + 1 := by
    have h := natDegree_hasseDeriv_le (rowPolynomial (-1) j) d
    rw [natDegree_rowPolynomial] at h
    exact Nat.lt_succ_of_le h
  rw [hshift, taylor_coeff, eval_eq_sum_range' hdeg]
  simp only [hasseDeriv_coeff, Nat.add_comm d]

/-- **Parisse's coefficients at $n$ from their values at $-1$.** Let $n \in \mathbb{Z}$. For
$j, k \in \mathbb{N}$ let $e_{j,k}(n)$ be the elementary symmetric polynomial of degree $k$ in
$n + 1, \dots, n + j$, let $b_{j,k}(n) = (-1)^k e_{j,j-k}(n)$ for $k \le j$ and $b_{j,k}(n) = 0$
for $k > j$, let
$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (k x + y)^\ell$ for complex $x, y$, with
$0^0 = 1$, and let
$c_{\ell,m}(n) = p_{\ell,m}(1, n + 1) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (k + n + 1)^\ell$. Then
$e_{j,k}(n) = \sum_{i=0}^{k} \binom{j - k + i}{i} (n + 1)^i e_{j,k-i}(-1)$ for all $k \le j$,
$b_{j,k}(n) = \sum_{i=k}^{j} (-1)^{i-k} \binom{i}{k} (n + 1)^{i-k} b_{j,i}(-1)$ for all $j, k$,
and $c_{\ell,m}(n) = \sum_{i=m}^{\ell} \binom{\ell}{i} (n + 1)^{\ell-i} c_{i,m}(-1)$ for all
$\ell, m \in \mathbb{N}$.

The first identity is stated only for $k \le j$; for $k > j$ the source's upper index
$j - k + i$ of the binomial coefficient can be negative.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Proposition 3 (`integers-2026-A36-prop-3`). -/
public theorem hyperseq_entries_eq_sum_at_neg_one (n : ℤ) :
    (∀ j k : ℕ, k ≤ j → ((Finset.Icc 1 j).val.map fun i : ℕ => n + i).esymm k =
      ∑ i ∈ Finset.range (k + 1), ((j - k + i).choose i : ℤ) * (n + 1) ^ i *
        ((Finset.Icc 1 j).val.map fun i : ℕ => (-1 : ℤ) + i).esymm (k - i)) ∧
    (∀ j k : ℕ, hyperseqB n j k =
      ∑ i ∈ Finset.Icc k j, (-1) ^ (i - k) * (i.choose k : ℤ) * (n + 1) ^ (i - k) *
        hyperseqB (-1) j i) ∧
    ∀ ℓ m : ℕ, alternatingBinomialPowerSum ℓ m 1 (n + 1) =
      ∑ i ∈ Finset.Icc m ℓ, (ℓ.choose i : ℂ) * ((n : ℂ) + 1) ^ (ℓ - i) *
        alternatingBinomialPowerSum i m 1 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro j k hk
    have hcoeff (a : ℤ) (d : ℕ) (hd : d ≤ j) : (rowPolynomial a j).coeff d =
        ((Icc 1 j).val.map fun i : ℕ => a + i).esymm (j - d) := by
      simpa [rowPolynomial, prod_map_val] using
        Multiset.prod_X_add_C_coeff' (Icc 1 j).val (fun i : ℕ => a + (i : ℤ))
          (k := d) (by simpa using hd)
    have hleft := hcoeff n (j - k) (Nat.sub_le _ _)
    rw [Nat.sub_sub_self hk] at hleft
    rw [← hleft, coeff_rowPolynomial_shift, Nat.sub_sub_self hk]
    refine sum_congr rfl fun i hi => ?_
    have hik := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [hcoeff (-1) (j - k + i) (by omega), show j - (j - k + i) = k - i by omega,
      Nat.choose_symm_add]
    ac_rfl
  · intro j k
    by_cases hk : k ≤ j
    · rw [hyperseqB_eq_neg_one_pow_mul_coeff, ← rowPolynomial, coeff_rowPolynomial_shift,
        mul_sum, ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range,
        show j + 1 - k = j - k + 1 by omega]
      refine sum_congr rfl fun i _ => ?_
      rw [hyperseqB_eq_neg_one_pow_mul_coeff, ← rowPolynomial, Nat.add_sub_cancel_left]
      have hsign : (-1 : ℤ) ^ i * (-1) ^ (k + i) = (-1) ^ k := by
        rw [pow_add, ← mul_assoc, mul_comm ((-1 : ℤ) ^ i), mul_assoc, ← mul_pow]
        simp
      rw [← hsign]
      ac_rfl
    · have hzero : (rowPolynomial n j).coeff k = 0 :=
        coeff_eq_zero_of_natDegree_lt (by simpa [natDegree_rowPolynomial] using Nat.lt_of_not_ge hk)
      rw [hyperseqB_eq_neg_one_pow_mul_coeff, ← rowPolynomial, hzero, mul_zero,
        Icc_eq_empty_of_lt (Nat.lt_of_not_ge hk), sum_empty]
  · intro ℓ m
    rw [(alternatingBinomialPowerSum_eq_sum_stirlingSecond 1 ((n : ℂ) + 1) ℓ m).1]
    refine sum_congr rfl fun i _ => ?_
    rw [(alternatingBinomialPowerSum_special_values 1 0 i m).2.2.2.1]
    simp only [one_pow, mul_one]
    ac_rfl

end MetaMathlibExt

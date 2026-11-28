/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.NarayanaSequence
public import MathlibExt.NumberTheory.SierpinskiRieselRepdigits
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Order.Preorder.Finite

/-!
# Sierpiński and Riesel numbers in Narayana's cows sequence

The sequence contains infinitely many distinct Sierpiński numbers. At indices congruent to
229972 modulo 718391520, the terms have a common residue modulo twice the product of the
six covering primes 3, 5, 7, 13, 17 and 241. The Riesel theorem uses a different cover by
exponent classes with the same six primes, together with the period modulo 2.
-/

namespace MetaMathlibExt

namespace NarayanaSierpinskiRiesel

open Matrix

private def step (p : ℕ) : Matrix (Fin 3) (Fin 3) (ZMod p) := !![0, 1, 0; 0, 0, 1; 1, 0, 1]

private def state (p n : ℕ) : Fin 3 → ZMod p :=
  ![narayanaCowsSequence n, narayanaCowsSequence (n + 1), narayanaCowsSequence (n + 2)]

private theorem state_eq (p n : ℕ) : state p n = (step p ^ n) *ᵥ ![0, 1, 1] := by
  induction n with
  | zero =>
    rw [pow_zero, one_mulVec]
    funext i
    fin_cases i <;> simp [state, narayanaCowsSequence]
  | succ n ih =>
    rw [pow_succ', ← mulVec_mulVec, ← ih]
    funext i
    fin_cases i <;> simp [state, step, mulVec, dotProduct, Fin.sum_univ_succ,
      narayanaCowsSequence]
    ac_rfl

private theorem binPow_eq_pow {M : Type*} [Monoid M] (x : M) (n : ℕ) :
    npowBinRec n x = x ^ n := by
  induction n with
  | zero => simp [npowBinRec_zero]
  | succ n ih => rw [npowBinRec_succ, ih, pow_succ]

private theorem residue (q : ℕ) :
    narayanaCowsSequence (229972 + 718391520 * q) ≡ 603713 [MOD 11184810] := by
  -- Repeated squaring verifies the period and the residue at the initial index.
  have hperiod : step 11184810 ^ 718391520 = 1 := by
    rw [← binPow_eq_pow]
    decide +kernel
  have hvalue : ((step 11184810 ^ 229972) *ᵥ ![0, 1, 1]) 0 = 603713 := by
    rw [← binPow_eq_pow]
    decide +kernel
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  change state 11184810 (229972 + 718391520 * q) 0 = 603713
  rw [state_eq, pow_add, pow_mul, hperiod, one_pow, mul_one]
  exact hvalue

private theorem sierpinski_of_residue {k : ℕ} (hk : k ≡ 603713 [MOD 11184810]) :
    IsSierpinskiNumber k := by
  refine ⟨Nat.odd_iff.mpr (hk.of_dvd (by decide : 2 ∣ 11184810)), ?_⟩
  intro n _
  -- For each exponent modulo 24, choose a divisor that works on the entire class.
  have hcover : ∀ r : Fin 24, ∃ p ∈ [3, 5, 7, 13, 17, 241],
      2 ≤ p ∧ p ≤ 241 ∧ p ∣ 11184810 ∧ 2 ^ 24 ≡ 1 [MOD p] ∧
      p ∣ 603713 * 2 ^ (r : ℕ) + 1 := by decide
  obtain ⟨p, _, hp, hple, hmod, hperiod, hr⟩ := hcover ⟨n % 24, Nat.mod_lt _ (by decide)⟩
  have hpow : 2 ^ n ≡ 2 ^ (n % 24) [MOD p] := by
    conv_lhs => rw [← Nat.mod_add_div n 24, pow_add, pow_mul]
    simpa only [one_pow, mul_one] using (hperiod.pow (n / 24)).mul_left (2 ^ (n % 24))
  have hfactor := ((((hk.of_dvd hmod).mul hpow).add_right 1).dvd_iff dvd_rfl).2 hr
  have hk_le : 603713 ≤ k := calc
    603713 = k % 11184810 := hk.symm
    _ ≤ k := Nat.mod_le _ _
  have := Nat.le_mul_of_pos_right k (by positivity : 0 < 2 ^ n)
  exact Nat.not_prime_of_dvd_of_lt hfactor hp (by omega)

private theorem lower_bound : ∀ n, n + 1 ≤ narayanaCowsSequence (n + 3)
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | n + 3 => by
    change n + 3 + 1 ≤ narayanaCowsSequence (n + 2 + 3) + narayanaCowsSequence (n + 3)
    have := lower_bound (n + 2)
    have := lower_bound n
    omega

private structure RieselClass where
  residue : ℕ
  modulus : ℕ
  prime : ℕ
  cowsPeriod : ℕ
  cowsResidue : ℕ

deriving DecidableEq

-- The exponent classes and paired primes of (1)–(2), with the sequence periods in Section 3.
private def rieselCover : List RieselClass :=
  [⟨1, 2, 3, 8, 2⟩, ⟨0, 3, 7, 57, 1⟩, ⟨0, 4, 5, 31, 1⟩,
    ⟨6, 8, 17, 288, 4⟩, ⟨2, 12, 13, 168, 10⟩, ⟨10, 24, 241, 9680, 237⟩]

private theorem exists_rieselClass (n : ℕ) :
    ∃ c ∈ rieselCover, n % c.modulus = c.residue := by
  have hcover : ∀ i : Fin 24, ∃ c ∈ rieselCover,
      c.modulus ∣ 24 ∧ (i : ℕ) % c.modulus = c.residue := by decide
  obtain ⟨c, hc, hd, hr⟩ := hcover ⟨n % 24, Nat.mod_lt _ (by decide)⟩
  exact ⟨c, hc, (Nat.mod_mod_of_dvd n hd).symm.trans hr⟩

private theorem rieselClass_spec : ∀ c ∈ rieselCover,
    c.prime.Prime ∧ c.prime ≤ 241 ∧ c.cowsPeriod ∣ 718391520 ∧
    2 ^ c.modulus ≡ 1 [MOD c.prime] ∧
    c.cowsResidue * 2 ^ c.residue ≡ 1 [MOD c.prime] := by decide +kernel

private theorem rieselClass_period (c : RieselClass) (hc : c ∈ rieselCover) :
    step c.prime ^ c.cowsPeriod = 1 := by
  rw [← binPow_eq_pow]
  exact (show ∀ c ∈ rieselCover, npowBinRec c.cowsPeriod (step c.prime) = 1 by
    decide +kernel) c hc

private theorem cows_modEq_of_period {p m t r a : ℕ} (hperiod : step p ^ m = 1)
    (htr : t ≡ r [MOD m])
    (hvalue : ((npowBinRec (r % m) (step p)) *ᵥ ![0, 1, 1]) 0 = (a : ZMod p)) :
    narayanaCowsSequence t ≡ a [MOD p] := by
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  change state p t 0 = (a : ZMod p)
  change t % m = r % m at htr
  rw [← htr, binPow_eq_pow] at hvalue
  conv_lhs => rw [← Nat.mod_add_div t m]
  rw [state_eq, pow_add, pow_mul, hperiod, one_pow, mul_one]
  exact hvalue

private theorem riesel_of_index {t : ℕ} {indices : Finset ℕ}
    (ht : t % 718391520 ∈ indices)
    (hcheck : ∀ r ∈ indices, 245 ≤ r ∧
      ((npowBinRec (r % 7) (step 2)) *ᵥ ![0, 1, 1]) 0 = 1 ∧
      ∀ c ∈ rieselCover,
        ((npowBinRec (r % c.cowsPeriod) (step c.prime)) *ᵥ ![0, 1, 1]) 0 =
          (c.cowsResidue : ZMod c.prime)) :
    IsRieselNumber (narayanaCowsSequence t) := by
  have htmod := (Nat.mod_modEq t 718391520).symm
  obtain ⟨hindex, hodd, hvalues⟩ := hcheck _ ht
  have hparity : step 2 ^ 7 = 1 := by
    rw [← binPow_eq_pow]
    decide +kernel
  refine ⟨Nat.odd_iff.mpr (cows_modEq_of_period hparity (htmod.of_dvd (by decide)) hodd), ?_⟩
  intro n _
  obtain ⟨c, hc, hn⟩ := exists_rieselClass n
  obtain ⟨hp, hple, hperiod, htwo, hinverse⟩ := rieselClass_spec c hc
  have hcows := cows_modEq_of_period (rieselClass_period c hc) (htmod.of_dvd hperiod) (hvalues c hc)
  have hpow : 2 ^ n ≡ 2 ^ c.residue [MOD c.prime] := by
    conv_lhs => rw [← Nat.mod_add_div n c.modulus, pow_add, pow_mul, hn]
    simpa only [one_pow, mul_one] using (htwo.pow (n / c.modulus)).mul_left (2 ^ c.residue)
  have hproduct := (hcows.mul hpow).trans hinverse
  have htge := hindex.trans (Nat.mod_le t 718391520)
  have hlarge := lower_bound (t - 3)
  rw [Nat.sub_add_cancel (by omega : 3 ≤ t)] at hlarge
  have hle := Nat.le_mul_of_pos_right (narayanaCowsSequence t) (by positivity : 0 < 2 ^ n)
  -- The product is at least 1, so subtracting 1 in ℕ gives the congruence difference.
  have hdiv := (Nat.modEq_iff_dvd' (by omega : 1 ≤ narayanaCowsSequence t * 2 ^ n)).mp
    hproduct.symm
  exact Nat.not_prime_of_dvd_of_lt hdiv hp.two_le (by omega)

end NarayanaSierpinskiRiesel

open NarayanaSierpinskiRiesel in
/-- **Infinitely many Narayana numbers are Sierpiński numbers.** There are infinitely many
natural numbers $k$ that are Sierpiński numbers and terms of Narayana's cows sequence $(N_t)$,
that is, $k = N_t$ for some $t$; here a Sierpiński number is an odd $k$ such that
$k \cdot 2^n + 1$ is not prime for every $n \ge 1$.

Source: Katherine Franzone and Joshua Harrington, *Sierpiński and Riesel Numbers in Narayana's
Cow Sequence*, INTEGERS 24 (2024), Article A10, Theorem 3 (`integers-2024-A10-thm-3`). -/
public theorem infinite_setOf_isSierpinskiNumber_narayanaCowsSequence :
    {k : ℕ | IsSierpinskiNumber k ∧ ∃ t, narayanaCowsSequence t = k}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro b
  refine ⟨_, ⟨sierpinski_of_residue (residue b), _, rfl⟩, ?_⟩
  have h := lower_bound (229969 + 718391520 * b)
  rw [show 229969 + 718391520 * b + 3 = 229972 + 718391520 * b by omega] at h
  omega

open NarayanaSierpinskiRiesel in
/-- **Narayana numbers that are Riesel numbers.** Let $(N_t)$ be Narayana's cows sequence, with
$N_0 = 0$ and $N_1 = N_2 = 1$. If $t$ is congruent modulo $718391520$ to one of the $27$ residues
$3629412$, $13386852$, $73151172$, $96325092$, $101203812$, $119499012$, $175604292$,
$198778212$, $212194692$, $240247332$, $268299972$, $328064292$, $337821732$, $360995652$,
$384169572$, $402464772$, $425638692$, $467107812$, $476865252$, $495160452$, $564682212$,
$587856132$, $592734852$, $611030052$, $629325252$, $652499172$, $703725732$, then $N_t$ is a
Riesel number: $N_t$ is odd and $N_t \cdot 2^n - 1$ is not prime for every $n \ge 1$.

With this indexing, $N_t$ is odd exactly when $t \bmod 7 \in \{1, 2, 3, 5\}$.

Source: Katherine Franzone and Joshua Harrington, *Sierpiński and Riesel Numbers in Narayana's
Cow Sequence*, INTEGERS 24 (2024), Article A10, Theorem 2 (`integers-2024-A10-thm-2`). -/
public theorem isRieselNumber_narayanaCowsSequence {t : ℕ}
    (ht : t % 718391520 ∈ ({3629412, 13386852, 73151172, 96325092, 101203812, 119499012,
      175604292, 198778212, 212194692, 240247332, 268299972, 328064292, 337821732, 360995652,
      384169572, 402464772, 425638692, 467107812, 476865252, 495160452, 564682212, 587856132,
      592734852, 611030052, 629325252, 652499172, 703725732} : Finset ℕ)) :
    IsRieselNumber (narayanaCowsSequence t) :=
  riesel_of_index ht (by decide +kernel)

end MetaMathlibExt

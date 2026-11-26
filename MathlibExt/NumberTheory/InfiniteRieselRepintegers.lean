/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SierpinskiRieselRepdigits
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.FieldTheory.Finite.Basic

/-!
# Infinitely many Riesel repintegers from a covering

The repinteger obtained by repeating the base-$b$ digits of $k$ has the same residues as $k$
modulo the covering primes along an arithmetic progression of repetition counts. Once the
repinteger exceeds all covering primes, each exponent has a proper divisor from the covering.

## References

* Chris Bispels, Matthew Cohen, Joshua Harrington, Joshua Lowrance, Kaelyn Pontes,
  Leif Schaumann, and Tony W. H. Wong, *On Sierpiński and Riesel Repdigits and Repintegers*,
  INTEGERS 26 (2026), [Article A12](https://math.colgate.edu/~integers/aa12/aa12.pdf), pp. 1–13.
  The residue-preservation argument adapts the proof of Theorem 3.3 (p. 5), which the authors
  identify as the model for Theorem 3.4. The Riesel divisibility step uses Section 2,
  Equation (3) (p. 4).
-/

namespace MetaMathlibExt

namespace infinite_riesel_repintegers

-- The geometric-sum and prime-modulus arguments generalize those for a single repeated digit in
-- `MathlibExt/NumberTheory/InfiniteRieselRepdigits.lean`.
private theorem repinteger_eq_sum {b k t : ℕ} (hB : 2 ≤ b ^ (Nat.digits b k).length) :
    repstring b k 0 t = k * ∑ i ∈ Finset.range t, (b ^ (Nat.digits b k).length) ^ i := by
  let B := b ^ (Nat.digits b k).length
  have hB₂ : 2 ≤ B := hB
  have hgeom := geom_sum_mul_of_one_le (by omega : 1 ≤ B) t
  have hpos : 0 < B - 1 := by omega
  rw [repstring, zero_add, pow_mul]
  change k * (B ^ t - 1) / (B - 1) = k * ∑ i ∈ Finset.range t, B ^ i
  rw [← hgeom, ← mul_assoc, Nat.mul_div_cancel _ hpos]

private theorem repinteger_modEq {b k t p : ℕ} (hp : p.Prime)
    (hB : 2 ≤ b ^ (Nat.digits b k).length) (ht : 1 ≤ t)
    (hpt : p ∣ t - 1) (hperiod : p - 1 ∣ t - 1) : repstring b k 0 t ≡ k [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  let B := b ^ (Nat.digits b k).length
  have hsum : ∑ i ∈ Finset.range t, (B : ZMod p) ^ i = 1 := by
    by_cases hB₁ : (B : ZMod p) = 1
    · have ht₁ : (t : ZMod p) = (1 : ℕ) := (ZMod.natCast_eq_natCast_iff t 1 p).2
        (((Nat.modEq_iff_dvd' ht).2 hpt).symm)
      simpa only [hB₁, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
        Nat.cast_one] using ht₁
    · have hpow : (B : ZMod p) ^ t = (B : ZMod p) := by
        by_cases hB₀ : (B : ZMod p) = 0
        · rw [hB₀, zero_pow (by omega : t ≠ 0)]
        · obtain ⟨q, hq⟩ := hperiod
          have ht_eq : t = (p - 1) * q + 1 := by omega
          rw [ht_eq, pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one hB₀, one_pow, one_mul,
            pow_one]
      apply mul_right_cancel₀ (sub_ne_zero.mpr hB₁)
      rw [geom_sum_mul, hpow, one_mul]
  rw [← ZMod.natCast_eq_natCast_iff, repinteger_eq_sum hB]
  change ((k * ∑ i ∈ Finset.range t, B ^ i : ℕ) : ZMod p) = k
  push_cast
  rw [hsum, mul_one]

private theorem riesel_of_covering {k N : ℕ} {S : Finset (ℕ × ℕ × ℕ)}
    (hk : 0 < k) (hS : IsRieselCoveringData k S) (hodd : Odd N)
    (hres : ∀ s ∈ S, N ≡ k [MOD s.2.2]) (hlarge : ∀ s ∈ S, s.2.2 < N) :
    IsRieselNumber N := by
  refine ⟨hodd, ?_⟩
  intro n hn
  obtain ⟨c, hc, hclass⟩ := hS.1 (n : ℤ)
  obtain ⟨⟨r, m, p⟩, hs, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨_, hp, hperiod, hfactor⟩ := hS.2.2 (r, m, p) hs
  have hnr : n ≡ r [MOD m] := Int.natCast_modEq_iff.mp hclass
  have hper : 2 ^ m ≡ 1 [MOD p] := ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).2 hperiod).symm
  have hreduce (j : ℕ) : 2 ^ j ≡ 2 ^ (j % m) [MOD p] := by
    conv_lhs => rw [← Nat.mod_add_div j m, pow_add, pow_mul]
    simpa only [one_pow, mul_one] using (hper.pow (j / m)).mul_left (2 ^ (j % m))
  have hpow : 2 ^ n ≡ 2 ^ r [MOD p] := calc
    2 ^ n ≡ 2 ^ (n % m) [MOD p] := hreduce n
    _ ≡ 2 ^ (r % m) [MOD p] := by rw [show n % m = r % m from hnr]
    _ ≡ 2 ^ r [MOD p] := (hreduce r).symm
  have hlt : p < N := hlarge (r, m, p) hs
  have hkr : 1 ≤ k * 2 ^ r := Nat.mul_pos hk (by positivity)
  have hkr_eq : k * 2 ^ r ≡ 1 [MOD p] := ((Nat.modEq_iff_dvd' hkr).2 hfactor).symm
  have hdvd : p ∣ N * 2 ^ n - 1 := (((hres (r, m, p) hs).mul hpow).trans hkr_eq).symm.dvd'
  have h2n : 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
  have hbound : N * 2 ≤ N * 2 ^ n := Nat.mul_le_mul_left N h2n
  exact Nat.not_prime_of_dvd_of_lt hdvd hp.two_le (by omega)

end infinite_riesel_repintegers

open infinite_riesel_repintegers in
/-- **Covering-produced Riesel numbers give infinitely many Riesel repintegers.** Let $k$ be a
Riesel number that has Riesel covering data, so that $k$ is produced as a Riesel number by the
covering system method. Then for every natural number $b \ge 2$ there are infinitely many $t \ge 1$
such that the $b$-repinteger $k_b^{(t)} = k\,(b^{\ell t} - 1)/(b^{\ell} - 1)$, where $\ell$ is the
number of base-$b$ digits of $k$ (so $k_b^{(t)}$ is $k$ written $t$ times in base $b$), is a Riesel
number.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.4 (stated in record
`integers-2026-A12-thm-3-3`). -/
public theorem infinite_riesel_repintegers {k : ℕ} (hk : IsRieselNumber k)
    {S : Finset (ℕ × ℕ × ℕ)} (hS : IsRieselCoveringData k S) {b : ℕ} (hb : 2 ≤ b) :
    {t : ℕ | 1 ≤ t ∧ IsRieselNumber (repstring b k 0 t)}.Infinite := by
  have hkpos : 0 < k := by obtain ⟨a, ha⟩ := hk.1; omega
  have hlen : 0 < (Nat.digits b k).length :=
    List.length_pos_iff.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr hkpos.ne')
  have hB : 2 ≤ b ^ (Nat.digits b k).length := hb.trans (by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ b) hlen)
  let L := 2 * ∏ s ∈ S, s.2.2 * (s.2.2 - 1)
  have hL : 0 < L := by
    refine Nat.mul_pos (by decide) (Finset.prod_pos fun s hs => ?_)
    have hp := (hS.2.2 s hs).2.1
    exact Nat.mul_pos hp.pos (by have := hp.two_le; omega)
  let P := ∑ s ∈ S, s.2.2
  apply Set.infinite_of_forall_exists_gt
  intro M
  let t := 1 + L * (M + P)
  have hstep : M + P ≤ L * (M + P) := Nat.le_mul_of_pos_left _ hL
  have ht : 1 ≤ t := by dsimp [t]; omega
  have htL : L ∣ t - 1 := ⟨M + P, by simp [t]⟩
  have hodd : Odd (repstring b k 0 t) := by
    have htwo : 2 ∣ L := dvd_mul_right _ _
    have hmod := repinteger_modEq Nat.prime_two hB ht (htwo.trans htL) (one_dvd _)
    exact Nat.odd_iff.mpr (by simpa [Nat.ModEq, Nat.odd_iff.mp hk.1] using hmod)
  have hres (s : ℕ × ℕ × ℕ) (hs : s ∈ S) : repstring b k 0 t ≡ k [MOD s.2.2] := by
    have hdiv : s.2.2 * (s.2.2 - 1) ∣ t - 1 :=
      (Finset.dvd_prod_of_mem _ hs).trans ((dvd_mul_left _ _).trans htL)
    exact repinteger_modEq (hS.2.2 s hs).2.1 hB ht
      ((dvd_mul_right _ _).trans hdiv) ((dvd_mul_left _ _).trans hdiv)
  have hrep : t ≤ repstring b k 0 t := by
    rw [repinteger_eq_sum hB]
    calc
      t = ∑ _i ∈ Finset.range t, 1 := by simp
      _ ≤ ∑ i ∈ Finset.range t, (b ^ (Nat.digits b k).length) ^ i :=
        Finset.sum_le_sum fun i _ => Nat.one_le_pow i _ (by omega)
      _ ≤ _ := Nat.le_mul_of_pos_left _ hkpos
  have hlarge (s : ℕ × ℕ × ℕ) (hs : s ∈ S) : s.2.2 < repstring b k 0 t := by
    have hsP : s.2.2 ≤ P := Finset.single_le_sum (f := fun x => x.2.2)
      (fun _ _ => Nat.zero_le _) hs
    exact lt_of_lt_of_le (by dsimp [t]; omega) hrep
  exact ⟨t, ⟨ht, riesel_of_covering hkpos hS hodd hres hlarge⟩, by dsimp [t]; omega⟩

end MetaMathlibExt

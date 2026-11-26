/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProductCongruence
import MathlibExt.Combinatorics.Enumerative.Partition.ReciprocalEulerDissection
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Regular cubic partitions with overlined odd parts

For $\ell=4$, the coefficients $a_4(n)$ of Buragohain and Saikia's Euler quotient in Eq. (2)
satisfy two congruences modulo four on prime-power progressions. A dissection of the reciprocal
fourth power of the Euler product identifies the coefficients at indices (4n+1) modulo four.
Euler's pentagonal number theorem then expresses the remaining coefficient modulo two as the
parity of a representation count for (x^2 + 8y^2).

At $\ell=4$ the quotient is the generating function of cubic partitions with odd parts overlined
and no part divisible by four, multiplied by $f_{16}/f_8=\prod_{m\ge1}(1+q^{8m})$, where
$f_k=\prod_{m\ge1}(1-q^{km})$. For example, $a_4(9)=130$, while $128$ cubic partitions of $9$
with odd parts overlined have no part divisible by four.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

local notation "𝔣" => qEulerProduct

/-- **Euler quotient for regular cubic partitions with odd parts overlined.** For a natural
number $\ell$, Buragohain and Saikia's Eq. (2) gives the integer power series
$$\frac{f_2 f_\ell^2 f_{4\ell}}{f_1^2 f_4 f_{2\ell}}, \qquad f_k = \prod_{m \ge 1} (1 - q^{km}).$$
For $\ell \ge 1$, the denominator has constant term $1$ and is invertible. At $\ell=4$, the
quotient equals the generating function obtained by forbidding all parts divisible by four
in cubic partitions with odd parts overlined, multiplied by
$f_{16}/f_8=\prod_{m\ge1}(1+q^{8m})$.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Section 1, eq. (2). -/
public noncomputable def regularCubicOverlinedSeries (l : ℕ) : ℤ⟦X⟧ :=
  𝔣 2 * 𝔣 l ^ 2 * 𝔣 (4 * l) * invOfUnit (𝔣 1 ^ 2 * 𝔣 4 * 𝔣 (2 * l)) 1

/-- **Coefficients of the regular cubic Euler quotient.** For natural numbers $\ell$ and $n$,
$a_\ell(n)$ is the coefficient of $q^n$ in Buragohain and Saikia's Eq. (2),
$$\frac{f_2 f_\ell^2 f_{4\ell}}{f_1^2 f_4 f_{2\ell}}, \qquad f_k = \prod_{m \ge 1} (1 - q^{km}).$$
For $\ell \ge 1$ the denominator has constant term $1$. For example, $a_3(5)=18$ and $a_4(9)=130$.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Section 1, eq. (2). -/
public noncomputable def regularCubicOverlinedCount (l n : ℕ) : ℤ :=
  coeff n (regularCubicOverlinedSeries l)

/-- **Generating function for the coefficients of the regular cubic Euler quotient.** Let
$\ell \ge 1$, write $f_k = \prod_{m \ge 1} (1 - q^{km})$ for the Euler products in the ring of
integer power series in $q$, and let $a_\ell(n)$ be the $n$th coefficient of
$f_2 f_\ell^2 f_{4\ell} / (f_1^2 f_4 f_{2\ell})$ (the denominator has constant term $1$, so it
is invertible). Then
$$
f_1^2 f_4 f_{2\ell} \sum_{n \ge 0} a_\ell(n) q^n = f_2 f_\ell^2 f_{4\ell}.
$$

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Section 1, eq. (2). -/
public theorem regularCubicOverlinedCount_generatingFunction {l : ℕ} (hl : 1 ≤ l) :
    𝔣 1 ^ 2 * 𝔣 4 * 𝔣 (2 * l) * PowerSeries.mk (regularCubicOverlinedCount l) =
      𝔣 2 * 𝔣 l ^ 2 * 𝔣 (4 * l) := by
  have hmk : PowerSeries.mk (regularCubicOverlinedCount l) = regularCubicOverlinedSeries l := by
    ext n
    simp [regularCubicOverlinedCount]
  have hc : constantCoeff (𝔣 1 ^ 2 * 𝔣 4 * 𝔣 (2 * l)) = ((1 : ℤˣ) : ℤ) := by
    simp [constantCoeff_qEulerProduct (le_refl 1),
      constantCoeff_qEulerProduct (by norm_num : 1 ≤ 4),
      constantCoeff_qEulerProduct (by omega : 1 ≤ 2 * l)]
  rw [hmk, regularCubicOverlinedSeries, mul_comm, mul_assoc, invOfUnit_mul _ _ hc, mul_one]

/-- **Constant term of the regular cubic Euler quotient.** For every natural number $\ell \ge 1$,
the constant coefficient $a_\ell(0)$ of the Euler quotient in Eq. (2) equals $1$.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Section 1, eq. (2). -/
public theorem regularCubicOverlinedCount_zero {l : ℕ} (hl : 1 ≤ l) :
    regularCubicOverlinedCount l 0 = 1 := by
  have h := congrArg (coeff 0) (regularCubicOverlinedCount_generatingFunction hl)
  simp only [coeff_zero_eq_constantCoeff, map_mul, map_pow,
    constantCoeff_qEulerProduct (le_refl 1), constantCoeff_qEulerProduct (by norm_num : 1 ≤ 2),
    constantCoeff_qEulerProduct (by norm_num : 1 ≤ 4), constantCoeff_qEulerProduct hl,
    constantCoeff_qEulerProduct (by omega : 1 ≤ 2 * l),
    constantCoeff_qEulerProduct (by omega : 1 ≤ 4 * l), one_pow, one_mul, mul_one] at h
  simpa using h

namespace regularCubicOverlinedCount_four_prime_mod_four

open scoped PowerSeries.WithPiTopology

private lemma product_expand (k : ℕ) (hk : k ≠ 0) :
    𝔣 k = expand k hk (pentagonalSeries ℤ) := by
  have cont : Continuous (expand k hk : ℤ⟦X⟧ → ℤ⟦X⟧) := by
    rw [continuous_iff_continuousAt]
    intro F
    rw [ContinuousAt, WithPiTopology.tendsto_iff_coeff_tendsto]
    intro n
    by_cases hd : k ∣ n
    · simpa [coeff_expand, hd] using (WithPiTopology.continuous_coeff ℤ (n / k)).tendsto F
    · simp [coeff_expand, hd]
  have prod := (WithPiTopology.hasProd_one_sub_X_pow ℤ).map (expand k hk) cont
  simpa [qEulerProduct, Function.comp_def, pow_mul] using prod.tprod_eq

private lemma twist_even (k : ℕ) (hk : k ≠ 0) :
    rescale (-1 : ℤ) (𝔣 (2 * k)) = 𝔣 (2 * k) := by
  rw [product_expand _ (by positivity)]
  ext n
  rw [coeff_rescale, coeff_expand]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    simp [mul_assoc, pow_mul]
  · simp

private abbrev reduce := PowerSeries.map (Int.castRingHom (ZMod 2))

private lemma reduce_double (k : ℕ) (hk : 0 < k) : reduce (𝔣 (k * 2)) = reduce (𝔣 k) ^ 2 := by
  rw [← map_pow]
  ext n
  simp only [coeff_map, Int.coe_castRingHom, ZMod.intCast_eq_intCast_iff]
  simpa using (qEulerProduct_iterated_primePower_congruence 2 1 k 1 1
    Nat.prime_two hk (by decide) (by decide) (by decide) n).symm

private lemma four_series : 𝔣 1 ^ 2 * 𝔣 8 * regularCubicOverlinedSeries 4 = 𝔣 2 * 𝔣 4 * 𝔣 16 := by
  have h := regularCubicOverlinedCount_generatingFunction (l := 4) (by decide)
  have hm : mk (regularCubicOverlinedCount 4) = regularCubicOverlinedSeries 4 := by
    ext n
    simp [regularCubicOverlinedCount]
  rw [hm] at h
  have h4 : 𝔣 4 ≠ 0 := fun e ↦ by
    simpa [e] using constantCoeff_qEulerProduct (k := 4) (by decide)
  apply mul_left_cancel₀ h4
  linear_combination h

/-- The odd part of the square of the generating function, with denominators cleared,
is given by the odd term of the dissection of the reciprocal fourth power. -/
private lemma base_coeff (n : ℕ) :
    regularCubicOverlinedCount 4 (4 * n + 1) ≡ 2 * coeff n (𝔣 1 * 𝔣 8) [ZMOD 4] := by
  let A := regularCubicOverlinedSeries 4
  let E : ℤ⟦X⟧ := mk fun j ↦ if Even j then coeff j A else 0
  let O := A - E
  have sum_eq : E + O = A := by dsimp [O]; ring
  have twist : rescale (-1 : ℤ) A = E - O := by
    ext j
    by_cases hj : Even j
    · simp [coeff_rescale, E, O, hj, hj.neg_one_pow]
    · simp [coeff_rescale, E, O, hj, (Nat.not_even_iff_odd.mp hj).neg_one_pow]
  let D := 𝔣 2 ^ 14 * 𝔣 8 ^ 6
  let N := 𝔣 2 * 𝔣 4 * 𝔣 16
  let K := N ^ 2 * 𝔣 2 ^ 4 * 𝔣 4 ^ 2 * 𝔣 8 ^ 8
  let L := N ^ 2 * 𝔣 4 ^ 14
  have hA : 𝔣 1 ^ 2 * 𝔣 8 * A = N := four_series
  have hs : D * A ^ 2 = L + 4 * X * K := by
    dsimp only [D, L, K]
    rw [← hA]
    linear_combination (𝔣 8 * A) ^ 2 * one_div_f1_pow_four_eight_twelve_two_dissection.1
  -- Subtract the identity at -X to isolate the product of the even and odd parts of A.
  have ht := congrArg (rescale (-1 : ℤ)) hs
  have t2 := twist_even 1 one_ne_zero
  have t4 := twist_even 2 two_ne_zero
  have t8 := twist_even 4 (by decide)
  have t16 := twist_even 8 (by decide)
  norm_num1 at t2 t4 t8 t16
  have twistD : rescale (-1 : ℤ) D = D := by simp [D, t2, t8]
  have twistK : rescale (-1 : ℤ) K = K := by simp [K, N, t2, t4, t8, t16]
  have twistL : rescale (-1 : ℤ) L = L := by simp [L, N, t2, t4, t16]
  simp only [map_mul, map_pow, map_add, map_ofNat, twistD, twistK, twistL, twist,
    rescale_neg_one_X] at ht
  rw [← sum_eq] at hs
  have heo : (D * E) * O = 2 * (X * K) := by
    apply mul_left_cancel₀ (show (4 : ℤ⟦X⟧) ≠ 0 from fun h ↦ by
      have := congrArg (constantCoeff (R := ℤ)) h
      simp only [map_ofNat, map_zero] at this
      contradiction)
    linear_combination hs - ht
  have hc : constantCoeff (D * E) = ((1 : ℤˣ) : ℤ) := by
    have hE : constantCoeff E = 1 := by
      rw [← coeff_zero_eq_constantCoeff_apply]
      dsimp only [E]
      simpa only [coeff_mk, ite_eq_left (show Even (0 : ℕ) from ⟨0, rfl⟩)] using
        (show coeff 0 A = 1 from regularCubicOverlinedCount_zero (l := 4) (by decide))
    simp [D, hE, constantCoeff_qEulerProduct (k := 2) (by decide),
      constantCoeff_qEulerProduct (k := 8) (by decide)]
  -- The unit D * E lets us divide the odd part by two over the integers.
  let H := invOfUnit (D * E) 1 * (X * K)
  have hH : (D * E) * H = X * K := by
    rw [show (D * E) * H = ((D * E) * invOfUnit (D * E) 1) * (X * K) by
      dsimp [H]; ring, mul_invOfUnit _ _ hc, one_mul]
  have hO : O = 2 * H := by
    apply mul_left_cancel₀ (show D * E ≠ 0 from fun h ↦ by simp [h] at hc)
    linear_combination heo - 2 * hH
  -- Modulo two, each Euler product with dyadic index is a power of the same series.
  let F := reduce (𝔣 1)
  have hnz : F ≠ 0 := fun h ↦ by
    have h' := congrArg (coeff 0) h
    simp only [F, reduce, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_qEulerProduct (k := 1) (by decide), map_one, map_zero, one_ne_zero] at h'
  have r2 : reduce (𝔣 2) = F ^ 2 := reduce_double 1 (by decide)
  have r4 : reduce (𝔣 4) = F ^ 4 := by rw [reduce_double 2 (by decide), r2, ← pow_mul]
  have r8 : reduce (𝔣 8) = F ^ 8 := by rw [reduce_double 4 (by decide), r4, ← pow_mul]
  have r16 : reduce (𝔣 16) = F ^ 16 := by rw [reduce_double 8 (by decide), r8, ← pow_mul]
  have r32 : reduce (𝔣 32) = F ^ 32 := by rw [reduce_double 16 (by decide), r16, ← pow_mul]
  have rA : reduce A = F ^ 12 := by
    have ha := congrArg reduce hA
    simp only [N, map_mul, map_pow, r2, r4, r8, r16] at ha
    apply mul_left_cancel₀ (pow_ne_zero 10 hnz)
    change F ^ 2 * F ^ 8 * reduce A = F ^ 2 * F ^ 4 * F ^ 16 at ha
    linear_combination ha
  have rE : reduce E = F ^ 12 := by
    rw [← rA, ← sum_eq, hO, map_add, map_mul, map_ofNat]
    have hz : (2 : (ZMod 2)⟦X⟧) = 0 := by
      simpa only [map_ofNat, map_zero] using congrArg (C (R := ZMod 2))
        (show (2 : ZMod 2) = 0 by decide)
    simp [hz]
  have rH : reduce H = reduce (X * (𝔣 4 * 𝔣 32)) := by
    have hh := congrArg reduce hH
    simp only [D, K, N, map_mul, map_pow, r2, r4, r8, r16, rE] at hh
    simp only [map_mul, r4, r32]
    apply mul_left_cancel₀ (pow_ne_zero 88 hnz)
    linear_combination hh
  have hex : expand 4 (by decide) (𝔣 1 * 𝔣 8) = 𝔣 4 * 𝔣 32 := by
    rw [map_mul, qEulerProduct_one, product_expand 4 (by decide), product_expand 8 (by decide),
      product_expand 32 (by decide), expand_mul 4 (by decide) 8 (by decide)]
  have hcoeff := congrArg (coeff (4 * n + 1)) rH
  simp only [reduce, coeff_map, Int.coe_castRingHom, ZMod.intCast_eq_intCast_iff,
    ← hex, X_mul, coeff_succ_mul_X, coeff_expand_mul] at hcoeff
  have hord := congrArg (coeff (4 * n + 1)) hO
  have hodd : ¬ Even (4 * n + 1) := by rw [Nat.even_iff]; omega
  simp only [O, E, map_sub, coeff_mk, ite_eq_right hodd, sub_zero, coeff_ofNat_mul] at hord
  change coeff (4 * n + 1) A ≡ _ [ZMOD 4]
  rw [hord]
  unfold Int.ModEq at *
  omega

/-- Completing the square in a generalized pentagonal number. -/
private lemma pentagonal_square (m : ℕ) :
    m ∈ Set.range pentagonal ↔ IsSquare (24 * m + 1) := by
  rw [← Int.isSquare_natCast_iff, isSquare_iff_exists_sq]
  push_cast
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨6 * k - 1, by linear_combination 12 * two_mul_natCast_pentagonal k⟩
  · rintro ⟨x, hx⟩
    have hr : x % 6 = 1 ∨ x % 6 = 5 := by
      have he : ((x % 6) * (x % 6)) % 6 = 1 := by
        rw [← Int.mul_emod, ← sq, ← hx]
        omega
      have hlo : 0 ≤ x % 6 := by omega
      have hhi : x % 6 < 6 := by omega
      generalize x % 6 = r at he hlo hhi ⊢
      interval_cases r <;> norm_num at *
    obtain ⟨z, hz⟩ : ∃ z : ℤ, z % 6 = 5 ∧ z ^ 2 = x ^ 2 := by
      rcases hr with hr | hr
      · exact ⟨-x, by omega, by ring⟩
      · exact ⟨x, hr, rfl⟩
    use (z + 1) / 6
    have he : 6 * ((z + 1) / 6) - 1 = z := by omega
    have hsq : 24 * (pentagonal ((z + 1) / 6) : ℤ) + 1 = z ^ 2 := by
      conv_rhs => rw [← he]
      linear_combination 12 * two_mul_natCast_pentagonal ((z + 1) / 6)
    exact_mod_cast (show (pentagonal ((z + 1) / 6) : ℤ) = m by linarith [hz.2])

/-- Modulo two, this series has a term at each square congruent to one modulo 24. -/
private noncomputable abbrev theta : (ZMod 2)⟦X⟧ :=
  X * expand 24 (by decide) (reduce (𝔣 1))
private noncomputable abbrev theta₈ : (ZMod 2)⟦X⟧ := expand 8 (by decide) theta

private lemma square_coeff (j : ℕ) :
    coeff j theta = if j % 24 = 1 ∧ IsSquare j then 1 else 0 := by
  classical
  obtain _ | j := j
  · simp [theta]
  rw [theta, X_mul, coeff_succ_mul_X, coeff_expand]
  by_cases h : 24 ∣ j
  · rw [ite_eq_left h]
    obtain ⟨m, rfl⟩ := h
    simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 24), reduce, coeff_map,
      qEulerProduct_one, Int.coe_castRingHom]
    by_cases hm : m ∈ Set.range pentagonal
    · have hs := (pentagonal_square m).mp hm
      obtain ⟨k, rfl⟩ := hm
      simp [hs, show (-1 : ZMod 2) = 1 by decide]
    · simp [coeff_pentagonalSeries_eq_zero ℤ hm, (pentagonal_square m).not.mp hm]
  · have hj : (j + 1) % 24 ≠ 1 := by omega
    simp [h, hj]

private lemma norm_coeff (n : ℕ) :
    coeff (24 * n + 9) (theta * theta₈) = ((coeff n (𝔣 1 * 𝔣 8) : ℤ) : ZMod 2) := by
  have hs : theta * theta₈ = expand 24 (by decide) (reduce (𝔣 1 * 𝔣 8)) * X ^ 9 := by
    rw [theta₈, theta, map_mul, expand_X, map_mul, map_mul, product_expand 8 (by decide),
      map_expand, ← qEulerProduct_one]
    have hc (f : (ZMod 2)⟦X⟧) :
        expand 8 (by decide) (expand 24 (by decide) f) =
          expand 24 (by decide) (expand 8 (by decide) f) := by
      rw [← expand_mul, ← expand_mul]
    rw [hc]
    ring
  rw [hs, coeff_mul_X_pow, coeff_expand_mul]
  rfl

private lemma prime_square_mod (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    p ^ 2 ≡ 1 [MOD 24] := by
  have hprime : p.Prime := Fact.out
  have h2 : ¬ 2 ∣ p := fun h ↦ by have := hprime.eq_one_or_self_of_dvd 2 h; omega
  have h3 : ¬ 3 ∣ p := fun h ↦ by have := hprime.eq_one_or_self_of_dvd 3 h; omega
  have h : p % 24 % 2 ≠ 0 ∧ p % 24 % 3 ≠ 0 := by omega
  change p ^ 2 % 24 = 1
  rw [Nat.pow_mod]
  have hl := Nat.mod_lt p (by decide : 0 < 24)
  generalize p % 24 = r at *
  interval_cases r <;> norm_num at *

private lemma square_scale (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (m : ℕ) :
    coeff (p ^ 2 * m) theta = coeff m theta := by
  have hm := (prime_square_mod p hp).mul_right m
  have hs : IsSquare (p ^ 2 * m) ↔ IsSquare m := by
    constructor
    · rintro ⟨x, hx⟩
      have prime : p.Prime := Fact.out
      have hd : p ∣ x * x := hx ▸ dvd_mul_of_dvd_left (dvd_pow_self p (by decide)) m
      obtain ⟨y, rfl⟩ := (prime.dvd_mul.mp hd).elim id id
      refine ⟨y, ?_⟩
      apply Nat.eq_of_mul_eq_mul_left (show 0 < p ^ 2 by positivity)
      linear_combination hx
    · rintro ⟨y, rfl⟩
      exact ⟨p * y, by ring⟩
  simp only [square_coeff, hs, show (p ^ 2 * m) % 24 = m % 24 by simpa [Nat.ModEq] using hm]

private lemma eight_square_scale (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (m : ℕ) :
    coeff (p ^ 2 * m) theta₈ = coeff m theta₈ := by
  by_cases h : 8 ∣ m
  · obtain ⟨k, rfl⟩ := h
    rw [Nat.mul_left_comm, theta₈, coeff_expand_mul, coeff_expand_mul, square_scale p hp]
  · have hm := ((prime_square_mod p hp).of_dvd (by decide : 8 ∣ 24)).mul_right m
    have hn : ¬ 8 ∣ p ^ 2 * m := by
      change _ % 8 = _ % 8 at hm
      simp only [one_mul] at hm
      omega
    simp only [theta₈, coeff_expand, h, hn, ite_false]

/-- At a prime inert in the form, divisibility of a represented value forces
divisibility of both coordinates. -/
private lemma prime_coordinates (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (hleg : legendreSym p (-2) = -1) (x y : ℕ) (hd : p ∣ x ^ 2 + 8 * y ^ 2) :
    p ∣ x ∧ p ∣ y := by
  have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  push_cast at hz
  have h2 : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 p).not.mpr
      (fun h ↦ by have := Nat.le_of_dvd (by decide : 0 < 2) h; omega)
  have hy : (y : ZMod p) = 0 := by
    by_contra hn
    apply (legendreSym.eq_neg_one_iff p).mp hleg
    refine ⟨(x : ZMod p) / (2 * y), ?_⟩
    push_cast
    field_simp
    linear_combination -hz
  have hx : (x : ZMod p) = 0 := by simpa [hy] using hz
  exact ⟨(ZMod.natCast_eq_zero_iff _ _).mp hx, (ZMod.natCast_eq_zero_iff _ _).mp hy⟩

/-- At a multiple of the prime, only terms with both exponents divisible by its square
contribute to the convolution. -/
private lemma norm_descent (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (hleg : legendreSym p (-2) = -1) (k : ℕ) (hk : p ∣ k) :
    coeff k (theta * theta₈) = coeff k (expand (p ^ 2) (by positivity) (theta * theta₈)) := by
  rw [map_mul (expand (p ^ 2) _) theta theta₈, coeff_mul k theta theta₈,
    coeff_mul k (expand _ _ theta) (expand _ _ theta₈)]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  have hsum : i + j = k := Finset.mem_antidiagonal.mp hij
  by_cases h : p ^ 2 ∣ i ∧ p ^ 2 ∣ j
  · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := h
    rw [coeff_expand_mul, coeff_expand_mul, square_scale p hp, eight_square_scale p hp]
  · have hl : coeff i theta * coeff j theta₈ = 0 := by
      by_contra hn
      have hi := left_ne_zero_of_mul hn
      have hj := right_ne_zero_of_mul hn
      rw [square_coeff] at hi
      split_ifs at hi with hc
      · obtain ⟨x, rfl⟩ := hc.2.exists_sq
        by_cases hd : 8 ∣ j
        · obtain ⟨b, rfl⟩ := hd
          rw [theta₈, coeff_expand_mul, square_coeff] at hj
          split_ifs at hj with hb
          · obtain ⟨y, rfl⟩ := hb.2.exists_sq
            obtain ⟨hx, hy⟩ := prime_coordinates p hp hleg x y (hsum ▸ hk)
            exact h ⟨pow_dvd_pow_of_dvd hx 2, dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hy 2) _⟩
          · contradiction
        · exact hj (coeff_expand_of_not_dvd 8 (by decide) theta hd)
      · contradiction
    rw [hl, eq_comm]
    by_cases hi : p ^ 2 ∣ i
    · rw [coeff_expand_of_not_dvd _ _ _ (show ¬ p ^ 2 ∣ j from fun hj ↦ h ⟨hi, hj⟩), mul_zero]
    · rw [coeff_expand_of_not_dvd _ _ _ hi, zero_mul]

private lemma iterated_descent (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (hleg : legendreSym p (-2) = -1) (δ m : ℕ) :
    coeff (p ^ (2 * δ) * m) (theta * theta₈) = coeff m (theta * theta₈) := by
  induction δ with
  | zero => simp
  | succ δ ih =>
    rw [show p ^ (2 * (δ + 1)) * m = p ^ 2 * (p ^ (2 * δ) * m) by
      rw [Nat.mul_succ, pow_add]; ring]
    rw [norm_descent p hp hleg _ (dvd_mul_of_dvd_left (dvd_pow_self p (show 2 ≠ 0 by decide)) _),
      coeff_expand_mul, ih]

private lemma count_from_norm {k : ℕ} (hk : k % 8 = 3) (v : ℤ)
    (hv : coeff (3 * k) (theta * theta₈) = (v : ZMod 2)) :
    regularCubicOverlinedCount 4 ((k - 1) / 2) ≡ 2 * v [ZMOD 4] := by
  obtain ⟨n, rfl⟩ : ∃ n, k = 8 * n + 3 := ⟨k / 8, by omega⟩
  rw [show 3 * (8 * n + 3) = 24 * n + 9 by ring, norm_coeff] at hv
  rw [show (8 * n + 3 - 1) / 2 = 4 * n + 1 by omega]
  apply (base_coeff n).trans
  have he := (ZMod.intCast_eq_intCast_iff _ _ _).mp hv
  unfold Int.ModEq at *
  omega

private lemma prime_progression (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (hleg : legendreSym p (-2) = -1) (δ n : ℕ) :
    regularCubicOverlinedCount 4 (4 * p ^ (2 * δ) * n + (3 * p ^ (2 * δ) - 1) / 2) ≡
      2 * coeff n (𝔣 1 * 𝔣 8) [ZMOD 4] := by
  let P := p ^ (2 * δ)
  have hp0 : 0 < P := by dsimp [P]; positivity
  have hP : P ≡ 1 [MOD 8] := by
    simpa [P, pow_mul] using ((prime_square_mod p hp).of_dvd (by decide : 8 ∣ 24)).pow δ
  have hk : (P * (8 * n + 3)) % 8 = 3 := by
    rw [Nat.mul_mod, show P % 8 = 1 from hP, one_mul]
    omega
  have he : (P * (8 * n + 3) - 1) / 2 = 4 * P * n + (3 * P - 1) / 2 := by
    have : P * (8 * n + 3) = 2 * (4 * P * n) + 3 * P := by ring
    omega
  rw [← he]
  apply count_from_norm hk
  rw [show 3 * (P * (8 * n + 3)) = P * (24 * n + 9) by ring,
    iterated_descent p hp hleg, norm_coeff]

private lemma vanishing_progression (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (hleg : legendreSym p (-2) = -1) (δ n t : ℕ) (ht : 1 ≤ t) (hlt : t ≤ p - 1) :
    regularCubicOverlinedCount 4 (4 * p ^ (2 * δ + 2) * n + 4 * p ^ (2 * δ + 1) * t +
      (3 * p ^ (2 * δ + 2) - 1) / 2) ≡ 0 [ZMOD 4] := by
  let P := p ^ (2 * δ)
  let m := p * (8 * n + 3) + 8 * t
  have hpp : p.Prime := Fact.out
  have hP : P ≡ 1 [MOD 8] := by
    simpa [P, pow_mul] using ((prime_square_mod p hp).of_dvd (by decide : 8 ∣ 24)).pow δ
  have hs := (prime_square_mod p hp).of_dvd (by decide : 8 ∣ 24)
  have hm : p * m = p ^ 2 * (8 * n + 3) + 8 * (p * t) := by dsimp [m]; ring
  have hk : (P * (p * m)) % 8 = 3 := by
    rw [Nat.mul_mod, show P % 8 = 1 from hP, one_mul, hm]
    have h : p ^ 2 * (8 * n + 3) ≡ 1 * (8 * n + 3) [MOD 8] := hs.mul_right _
    unfold Nat.ModEq at h
    omega
  have he : (P * (p * m) - 1) / 2 =
      4 * p ^ (2 * δ + 2) * n + 4 * p ^ (2 * δ + 1) * t +
        (3 * p ^ (2 * δ + 2) - 1) / 2 := by
    have h : P * (p * m) = 2 * (4 * p ^ (2 * δ + 2) * n + 4 * p ^ (2 * δ + 1) * t) +
        3 * p ^ (2 * δ + 2) := by simp only [P, m, pow_add]; ring
    have : 0 < p ^ (2 * δ + 2) := by positivity
    omega
  rw [← he]
  apply (count_from_norm hk 0 ?_).trans (by simp)
  rw [show 3 * (P * (p * m)) = P * (p * (3 * m)) by ring, iterated_descent p hp hleg,
    norm_descent p hp hleg _ (dvd_mul_right p (3 * m))]
  apply coeff_expand_of_not_dvd
  rw [pow_two, Nat.mul_dvd_mul_iff_left (by omega : 0 < p)]
  have h3 : ¬ p ∣ 3 := fun h ↦ by have := Nat.le_of_dvd (by decide : 0 < 3) h; omega
  have h2 : ¬ p ∣ 2 := fun h ↦ by have := Nat.le_of_dvd (by decide : 0 < 2) h; omega
  have h8 : ¬ p ∣ 8 := fun h ↦ h2 (hpp.dvd_of_dvd_pow (n := 3) h)
  have hnt : ¬ p ∣ t := fun h ↦ by have := Nat.le_of_dvd ht h; omega
  intro h
  have hd := (hpp.dvd_mul.mp h).resolve_left h3
  have hdt : p ∣ 8 * t := (Nat.dvd_add_right (dvd_mul_right p (8 * n + 3))).mp hd
  exact (hpp.dvd_mul.mp hdt).elim h8 hnt

end regularCubicOverlinedCount_four_prime_mod_four

/-- **Prime congruences modulo 4 for the regular cubic Euler quotient at $\ell=4$.** Write
$f_k = \prod_{m \ge 1} (1 - q^{km})$ for the Euler products in the ring of integer power series
in $q$, and let $a_4(n)$ be the coefficient of $q^n$ in Buragohain and Saikia's Eq. (2)
at $\ell=4$, namely $f_2 f_4^2 f_{16} / (f_1^2 f_4 f_8)$. Let $p \ge 5$ be a prime
with Legendre symbol $\left(\frac{-2}{p}\right) = -1$ and let $\delta \ge 0$. Then for every
$n \ge 0$, $a_4(4p^{2\delta} n + (3p^{2\delta} - 1)/2)$ is congruent modulo $4$ to twice the
coefficient of $q^n$ in $f_1 f_8$, and for all $n \ge 0$ and $1 \le t \le p - 1$,
$$
a_4\left(4p^{2\delta+2} n + 4p^{2\delta+1} t + \frac{3p^{2\delta+2} - 1}{2}\right) \equiv 0
\pmod{4}.
$$

The divisions by $2$ are exact. At $\delta=0$ and $n=2$, the first congruence reads
$a_4(9)\equiv 2\pmod 4$. The coefficient is $130$. Forbidding all parts divisible by four
in cubic partitions with odd parts overlined gives $128$ partitions of $9$.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 8, eq. (49)
and the unnumbered congruence after it (`integers-2024-A101-thm-8`). -/
public theorem regularCubicOverlinedCount_four_prime_mod_four (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hleg : legendreSym p (-2) = -1) (δ : ℕ) :
    (∀ n : ℕ, regularCubicOverlinedCount 4 (4 * p ^ (2 * δ) * n + (3 * p ^ (2 * δ) - 1) / 2) ≡
        2 * coeff n (𝔣 1 * 𝔣 8) [ZMOD 4]) ∧
      ∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 4 (4 * p ^ (2 * δ + 2) * n + 4 * p ^ (2 * δ + 1) * t +
          (3 * p ^ (2 * δ + 2) - 1) / 2) ≡ 0 [ZMOD 4] := by
  exact ⟨regularCubicOverlinedCount_four_prime_mod_four.prime_progression p hp hleg δ,
    regularCubicOverlinedCount_four_prime_mod_four.vanishing_progression p hp hleg δ⟩

end

end MetaMathlibExt

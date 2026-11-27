/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Real.Irrational
public import MathlibExt.NumberTheory.ChoosePowMulModEq
public import MathlibExt.NumberTheory.ExistsUniqueRadicalExpansionCoeffs
public import MathlibExt.NumberTheory.GcdPowAddNegOnePow
public import MathlibExt.NumberTheory.PrimeDvdChoosePowMulPowMul
public import MathlibExt.NumberTheory.PrimeDvdPowAddOfDvdRadicalCoeffsGcd
public import MathlibExt.NumberTheory.RadicalCoefficientCommonPrime
public import MathlibExt.NumberTheory.RadicalCoefficientGcdStep
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Tactic.LinearCombination

/-!
# Greatest common divisors of square-root expansion coefficients

The gcd of the integer coefficients of `(u + √v) ^ n` is a power of two determined by
`u ^ 2 - v`, for positive coprime `u` and `v` with irrational `√v`.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Theorem 17
(`jis-2025-25.2.2-thm-17`).
-/

namespace MetaMathlibExt
private def alpha (u v : ℕ) : Zsqrtd v := ⟨u, 1⟩
private theorem nonsquare {v : ℕ} (hirr : Irrational (Real.sqrt v)) (q : ℚ) :
    q ^ 2 ≠ (v : ℚ) := by
  intro h
  have hreal : (q : ℝ) ^ 2 = v := by exact_mod_cast h
  apply hirr.ne_rat |q|
  rw [← hreal, Real.sqrt_sq_eq_abs, Rat.cast_abs]
private theorem coeffs {u v : ℕ} (hirr : Irrational (Real.sqrt v)) (a b : ℕ → ℤ)
    (hab : ∀ n, 1 ≤ n → ((u : ℝ) + Real.sqrt v) ^ n = a n + b n * Real.sqrt v)
    (n : ℕ) (hn : 1 ≤ n) : alpha u v ^ n = ⟨a n, b n⟩ := by
  let root : {r : ℝ // r * r = ((v : ℤ) : ℝ)} :=
    ⟨Real.sqrt v, by simp [← pow_two, Real.sq_sqrt (Nat.cast_nonneg v)]⟩
  apply Zsqrtd.lift_injective root
  · intro z hz
    apply nonsquare hirr (z : ℚ)
    simpa only [pow_two] using (show (z : ℚ) * z = v by exact_mod_cast hz.symm)
  · simpa [map_pow, Zsqrtd.lift_apply_apply, root, alpha] using hab n hn
private theorem only_two {u v : ℕ} (huv : u.Coprime v)
    (hirr : Irrational (Real.sqrt v)) (a b : ℕ → ℤ)
    (hab : ∀ n, 1 ≤ n → ((u : ℝ) + Real.sqrt v) ^ n = a n + b n * Real.sqrt v)
    (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime)
    (hpd : p ∣ Int.gcd (a n) (b n)) : p = 2 := by
  have hi : Irreducible (Polynomial.X ^ 2 - Polynomial.C (v : ℚ)) :=
    irreducible_X_pow_sub_C_of_prime Nat.prime_two (nonsquare hirr)
  let c : ℕ → Fin 2 → ℤ := fun m i ↦ if i = 0 then a m else b m
  have hc (m : ℕ) (hm : 1 ≤ m) :
      ((u : ℝ) + (v : ℝ) ^ (1 / (2 : ℝ))) ^ m =
        ∑ i : Fin 2, (c m i : ℝ) * ((v : ℝ) ^ (1 / (2 : ℝ))) ^ (i : ℕ) := by
    simpa [c, Fin.sum_univ_succ, Real.sqrt_eq_rpow] using hab m hm
  have hpc : (p : ℤ) ∣ Finset.univ.gcd (c n) := by
    apply Finset.dvd_gcd
    intro i _
    have hpg : (p : ℤ) ∣ (Int.gcd (a n) (b n) : ℤ) := Int.natCast_dvd_natCast.mpr hpd
    dsimp [c]
    split
    · exact hpg.trans (Int.gcd_dvd_left _ _)
    · exact hpg.trans (Int.gcd_dvd_right _ _)
  have hpn := prime_dvd_pow_add_of_dvd_radical_coeffs_gcd hi c hc n hn p hp hpc
  have hp2 := prime_dvd_gcd_pow_add_radical_coeffs (by decide : 2 ≤ 2) huv hi c hc
    n hn p hp ((dvd_gcd_iff ..).mpr ⟨hpn, hpc⟩)
  exact ((Nat.dvd_prime Nat.prime_two).mp hp2).resolve_left hp.ne_one
private theorem scaled_gcd {v : ℕ} (w z : Zsqrtd v) (k : ℕ) (hw0 : w ≠ 0)
    (hw : w = ((2 : ℤ) ^ k : Zsqrtd v) * z)
    (hp : ∀ p : ℕ, p.Prime → p ∣ Int.gcd w.re w.im → p = 2)
    (hz : ¬ (2 : ℤ) ∣ z.re ∨ ¬ (2 : ℤ) ∣ z.im) :
    Int.gcd w.re w.im = 2 ^ k := by
  have hz0 : z ≠ 0 := by
    intro hz0
    apply hw0
    simp [hw, hz0]
  have hpos := (Zsqrtd.gcd_pos_iff z).mpr hz0
  have hcop : Int.gcd z.re z.im = 1 := by
    apply Nat.le_antisymm ?_ hpos
    by_contra hle
    obtain ⟨p, hprime, hpg⟩ := Nat.exists_prime_and_dvd
      (by omega : Int.gcd z.re z.im ≠ 1)
    have hpr : (p : ℤ) ∣ z.re :=
      (Int.natCast_dvd_natCast.mpr hpg).trans (Int.gcd_dvd_left _ _)
    have hpi : (p : ℤ) ∣ z.im :=
      (Int.natCast_dvd_natCast.mpr hpg).trans (Int.gcd_dvd_right _ _)
    have hpow : p ∣ Int.gcd w.re w.im := by
      rw [hw]
      simp only [← Int.cast_pow, Zsqrtd.re_smul, Zsqrtd.im_smul]
      apply Int.dvd_gcd
      · exact dvd_mul_of_dvd_right hpr _
      · exact dvd_mul_of_dvd_right hpi _
    obtain rfl := hp p hprime hpow
    exact hz.elim (fun h ↦ h hpr) (fun h ↦ h hpi)
  rw [hw]
  simp only [← Int.cast_pow, Zsqrtd.re_smul, Zsqrtd.im_smul, Int.gcd_mul_left]
  simp [hcop, Int.natAbs_pow]

private theorem odd_norm_not_both {v : ℕ} (z : Zsqrtd v) (hz : Odd z.norm) :
    ¬ (2 : ℤ) ∣ z.re ∨ ¬ (2 : ℤ) ∣ z.im := by
  by_contra! h
  have hd : (2 : ℤ) ∣ z.norm :=
    dvd_sub (dvd_mul_of_dvd_left h.1 _) (dvd_mul_of_dvd_right h.2 _)
  have hd0 := Int.emod_eq_zero_of_dvd hd
  have hd1 := Int.odd_iff.mp hz
  omega
private theorem odd_mul {v : ℕ} (hv : (v : ℤ) % 2 = 1) (w z : Zsqrtd v)
    (hr : w.re % 2 = 1) (hi : w.im % 2 = 1) (hz : Odd z.norm) :
    (w * z).re % 2 = 1 ∧ (w * z).im % 2 = 1 := by
  have hn := Int.odd_iff.mp hz
  have hr0 : 0 ≤ z.re % 2 := Int.emod_nonneg _ (by decide)
  have hr2 : z.re % 2 < 2 := Int.emod_lt_of_pos _ (by decide)
  have hi0 : 0 ≤ z.im % 2 := Int.emod_nonneg _ (by decide)
  have hi2 : z.im % 2 < 2 := Int.emod_lt_of_pos _ (by decide)
  interval_cases hzr : z.re % 2 <;> interval_cases hzi : z.im % 2 <;>
    norm_num [Zsqrtd.norm, Zsqrtd.re_mul, Zsqrtd.im_mul, Int.add_emod,
      Int.sub_emod, Int.mul_emod, hv, hr, hi, hzr, hzi] at hn <;>
    norm_num [Zsqrtd.re_mul, Zsqrtd.im_mul, Int.add_emod, Int.mul_emod,
      hv, hr, hi, hzr, hzi]
private theorem norm_pow {v : ℕ} (z : Zsqrtd v) (n : ℕ) :
    (z ^ n).norm = z.norm ^ n := (Zsqrtd.normMonoidHom (d := v)).map_pow z n

private theorem odd_uv {u v : ℕ} (huv : u.Coprime v)
    (h : ((u : ℤ) ^ 2 - v) % 2 = 0) : (u : ℤ) % 2 = 1 ∧ (v : ℤ) % 2 = 1 := by
  have hsame : ((u : ℤ) % 2 - (v : ℤ) % 2) % 2 = 0 := by
    simpa only [Int.sub_emod, Int.sq_emod_two, Int.emod_emod] using h
  have hu0 : (u : ℤ) % 2 ≠ 0 := by
    intro hu0
    have hv0 : (v : ℤ) % 2 = 0 := by omega
    have hd := Int.dvd_gcd (Int.dvd_of_emod_eq_zero hu0) (Int.dvd_of_emod_eq_zero hv0)
    rw [Int.gcd_natCast_natCast, huv.gcd_eq_one] at hd
    norm_num at hd
  omega
private theorem odd_sq_mod_eight (u : ℤ) (hu : u % 2 = 1) : u ^ 2 % 8 = 1 := by
  have h0 : 0 ≤ u % 8 := Int.emod_nonneg _ (by decide)
  have h8 : u % 8 < 8 := Int.emod_lt_of_pos _ (by decide)
  interval_cases hmod : u % 8 <;> try omega
  all_goals norm_num [pow_two, Int.mul_emod, hmod]
private theorem square_block {u v : ℕ} (t : ℤ)
    (h : (u : ℤ) ^ 2 - v = 4 * t + 2) :
    ∃ z : Zsqrtd v, alpha u v ^ 2 = 2 * z ∧ Odd z.norm := by
  let z : Zsqrtd v := ⟨(u : ℤ) ^ 2 - 2 * t - 1, u⟩
  have hv : (v : ℤ) = (u : ℤ) ^ 2 - 4 * t - 2 := by omega
  refine ⟨z, ?_, ?_⟩
  · ext <;> simp [alpha, z, pow_two, hv] <;> ring
  · have hn : z.norm = (2 * t + 1) ^ 2 := by
      dsimp [z, Zsqrtd.norm]
      rw [hv]
      ring
    rw [hn]
    exact (show Odd (2 * t + 1) from ⟨t, rfl⟩).pow
private theorem cube_block {u v : ℕ} (t r : ℤ)
    (h : (u : ℤ) ^ 2 - v = 8 * t + 4) (hs : (u : ℤ) ^ 2 = 8 * r + 1) :
    ∃ z : Zsqrtd v, alpha u v ^ 3 = 8 * z ∧ Odd z.norm := by
  let z : Zsqrtd v := ⟨(u : ℤ) * (4 * r - 3 * t - 1), 4 * r - t⟩
  have hv : (v : ℤ) = 8 * r - 8 * t - 3 := by omega
  refine ⟨z, ?_, ?_⟩
  · ext <;> simp [alpha, z, pow_succ, hv]
    · linear_combination (u : ℤ) * hs
    · linear_combination 3 * hs
  · have hn : z.norm = (2 * t + 1) ^ 3 := by
      calc
        z.norm = (u : ℤ) ^ 2 * (4 * r - 3 * t - 1) ^ 2 -
            (v : ℤ) * (4 * r - t) ^ 2 := by dsimp [z, Zsqrtd.norm]; ring
        _ = (2 * t + 1) ^ 3 := by rw [hs, hv]; ring
    rw [hn]
    exact (show Odd (2 * t + 1) from ⟨t, rfl⟩).pow

private theorem half_step {u v : ℕ} (t : ℤ)
    (hu : (u : ℤ) % 2 = 1) (h : (u : ℤ) ^ 2 - v = 8 * t)
    (z : Zsqrtd v) (hi : z.im % 2 = 1) (hr : (z.re - u * z.im) % 4 = 0) :
    ∃ w : Zsqrtd v, alpha u v * z = 2 * w ∧ w.re % 2 = 1 ∧
      w.im % 2 = 1 ∧ (w.re - u * w.im) % 4 = 0 := by
  obtain ⟨s, hs⟩ := Int.dvd_of_emod_eq_zero hr
  have hA : z.re = u * z.im + 4 * s := by omega
  have hv : (v : ℤ) = (u : ℤ) ^ 2 - 8 * t := by omega
  let w : Zsqrtd v :=
    ⟨((u : ℤ) ^ 2 - 4 * t) * z.im + 2 * u * s, u * z.im + 2 * s⟩
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · ext <;> simp [alpha, w, hA, hv] <;> ring
  · norm_num [w, pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, hu, hi]
  · norm_num [w, Int.add_emod, Int.mul_emod, hu, hi]
  · have he : w.re - u * w.im = 4 * (-t * z.im) := by dsimp [w]; ring
    rw [he]
    omega
private theorem repeated_halving {u v : ℕ} (t : ℤ)
    (hu : (u : ℤ) % 2 = 1) (h : (u : ℤ) ^ 2 - v = 8 * t) (m : ℕ) :
    ∃ z : Zsqrtd v, alpha u v ^ (m + 1) = 2 ^ m * z ∧
      z.re % 2 = 1 ∧ z.im % 2 = 1 ∧ (z.re - u * z.im) % 4 = 0 := by
  induction m with
  | zero => exact ⟨alpha u v, by simp, hu, by simp [alpha], by simp [alpha]⟩
  | succ m ih =>
    obtain ⟨z, hz, _, hi, hr⟩ := ih
    obtain ⟨w, hw, hwr, hwi, hratio⟩ := half_step t hu h z hi hr
    refine ⟨w, ?_, hwr, hwi, hratio⟩
    calc
      alpha u v ^ (m + 1 + 1) = alpha u v * alpha u v ^ (m + 1) := pow_succ' _ _
      _ = alpha u v * (2 ^ m * z) := by rw [hz]
      _ = 2 ^ m * (alpha u v * z) := by ring
      _ = 2 ^ m * (2 * w) := by rw [hw]
      _ = 2 ^ (m + 1) * w := by rw [pow_succ]; ring


@[expose] public section

/-- **Gcd of the coefficients of $(u + \sqrt{v})^n$.** Let $u, v$ be coprime positive integers
with $\sqrt{v}$ irrational, let $a_n, b_n$ (for natural $n$) be integers with
$(u + \sqrt{v})^n = a_n + b_n \sqrt{v}$ for every $n \ge 1$, and let $D_n \ge 0$ be the greatest
common divisor of $a_n$ and $b_n$. Then for every $n \ge 1$:
(a) if $u^2 - v$ is odd, then $D_n = 1$;
(b) if $u^2 - v \equiv 2 \pmod 4$, then $D_{2n-1} = 2^{n-1}$ and $D_{2n} = 2^n$;
(c) if $u^2 - v \equiv 4 \pmod 8$, then $D_{3n-2} = 2^{3n-3}$, $D_{3n-1} = 2^{3n-2}$ and
$D_{3n} = 2^{3n}$;
(d) if $u^2 - v \equiv 0 \pmod 8$, then $D_n = 2^{n-1}$.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Theorem 17
(`jis-2025-25.2.2-thm-17`). -/
public theorem gcd_sqrt_expansion_coeffs {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (huv : u.Coprime v) (hirr : Irrational (Real.sqrt v)) (a b : ℕ → ℤ)
    (hab : ∀ n, 1 ≤ n → ((u : ℝ) + Real.sqrt v) ^ n = a n + b n * Real.sqrt v) :
    (Odd ((u : ℤ) ^ 2 - v) → ∀ n, 1 ≤ n → Int.gcd (a n) (b n) = 1) ∧
    (((u : ℤ) ^ 2 - v) % 4 = 2 → ∀ n, 1 ≤ n →
      Int.gcd (a (2 * n - 1)) (b (2 * n - 1)) = 2 ^ (n - 1) ∧
        Int.gcd (a (2 * n)) (b (2 * n)) = 2 ^ n) ∧
    (((u : ℤ) ^ 2 - v) % 8 = 4 → ∀ n, 1 ≤ n →
      Int.gcd (a (3 * n - 2)) (b (3 * n - 2)) = 2 ^ (3 * n - 3) ∧
        Int.gcd (a (3 * n - 1)) (b (3 * n - 1)) = 2 ^ (3 * n - 2) ∧
        Int.gcd (a (3 * n)) (b (3 * n)) = 2 ^ (3 * n)) ∧
    (((u : ℤ) ^ 2 - v) % 8 = 0 → ∀ n, 1 ≤ n → Int.gcd (a n) (b n) = 2 ^ (n - 1))
    := by
  have hpositive : 0 < (u : ℝ) + Real.sqrt v :=
    add_pos (Nat.cast_pos.mpr hu) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hv))
  have hnonzero (n : ℕ) : alpha u v ^ n ≠ 0 := by
    let root : {r : ℝ // r * r = ((v : ℤ) : ℝ)} :=
      ⟨Real.sqrt v, by simp [← pow_two, Real.sq_sqrt (Nat.cast_nonneg v)]⟩
    intro hz
    have h := congrArg (Zsqrtd.lift root) hz
    have hpow : ((u : ℝ) + Real.sqrt v) ^ n = 0 := by
      simpa [map_pow, Zsqrtd.lift_apply_apply, root, alpha] using h
    exact (pow_pos hpositive n).ne' hpow
  have heq (n : ℕ) (hn : 1 ≤ n) :
      Int.gcd (alpha u v ^ n).re (alpha u v ^ n).im = Int.gcd (a n) (b n) := by
    rw [coeffs hirr a b hab n hn]
  have hp (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hprime : p.Prime)
      (hpd : p ∣ Int.gcd (alpha u v ^ n).re (alpha u v ^ n).im) : p = 2 :=
    only_two huv hirr a b hab n hn p hprime (heq n hn ▸ hpd)
  have finish (n : ℕ) (hn : 1 ≤ n) (z : Zsqrtd v) (k : ℕ)
      (hw : alpha u v ^ n = 2 ^ k * z)
      (hz : ¬ (2 : ℤ) ∣ z.re ∨ ¬ (2 : ℤ) ∣ z.im) :
      Int.gcd (a n) (b n) = 2 ^ k := by
    rw [← heq n hn]
    exact scaled_gcd _ z k (hnonzero n) hw (hp n hn) hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hd n hn
    have hnorm : Odd (alpha u v ^ n).norm := by
      rw [norm_pow]
      simpa [alpha, Zsqrtd.norm, pow_two] using hd.pow (n := n)
    exact finish n hn (alpha u v ^ n) 0 (by simp) (odd_norm_not_both _ hnorm)
  · intro hd n hn
    obtain ⟨huo, hvo⟩ := odd_uv huv (by omega)
    obtain ⟨t, ht⟩ : ∃ t : ℤ, (u : ℤ) ^ 2 - v = 4 * t + 2 :=
      ⟨((u : ℤ) ^ 2 - v) / 4, by omega⟩
    obtain ⟨z, hz, hzn⟩ := square_block t ht
    have hblock (m : ℕ) : alpha u v ^ (2 * m) = 2 ^ m * z ^ m := by
      rw [pow_mul, hz, mul_pow]
    have hnorm (m : ℕ) : Odd (z ^ m).norm := by rw [norm_pow]; exact hzn.pow
    constructor
    · have hindex : 2 * n - 1 = 2 * (n - 1) + 1 := by omega
      have hscale : alpha u v ^ (2 * n - 1) =
          2 ^ (n - 1) * (alpha u v * z ^ (n - 1)) := by
        rw [hindex, pow_succ', hblock]
        ring
      have hod := odd_mul hvo (alpha u v) (z ^ (n - 1)) huo (by simp [alpha])
        (hnorm (n - 1))
      exact finish _ (by omega) _ _ hscale (Or.inl (Int.two_dvd_ne_zero.mpr hod.1))
    · exact finish _ (by omega) _ _ (hblock n) (odd_norm_not_both _ (hnorm n))
  · intro hd n hn
    obtain ⟨huo, hvo⟩ := odd_uv huv (by omega)
    obtain ⟨t, ht⟩ : ∃ t : ℤ, (u : ℤ) ^ 2 - v = 8 * t + 4 :=
      ⟨((u : ℤ) ^ 2 - v) / 8, by omega⟩
    obtain ⟨r, hr⟩ : ∃ r : ℤ, (u : ℤ) ^ 2 = 8 * r + 1 :=
      ⟨(u : ℤ) ^ 2 / 8, by have hs := odd_sq_mod_eight (u : ℤ) huo; omega⟩
    obtain ⟨z, hz, hzn⟩ := cube_block t r ht hr
    have hblock (m : ℕ) : alpha u v ^ (3 * m) = 2 ^ (3 * m) * z ^ m := by
      rw [pow_mul, hz, mul_pow, show (8 : Zsqrtd v) = 2 ^ 3 by norm_num, ← pow_mul]
    have hnorm (m : ℕ) : Odd (z ^ m).norm := by rw [norm_pow]; exact hzn.pow
    let w : Zsqrtd v := ⟨(u : ℤ) ^ 2 - 4 * t - 2, u⟩
    have hw : alpha u v ^ 2 = 2 * w := by
      have hV : (v : ℤ) = (u : ℤ) ^ 2 - 8 * t - 4 := by omega
      ext <;> simp [alpha, w, pow_two, hV] <;> ring
    have hwr : w.re % 2 = 1 := by
      norm_num [w, Int.sub_emod, Int.mul_emod, Int.sq_emod_two, huo]
    refine ⟨?_, ?_, ?_⟩
    · have hindex : 3 * n - 2 = 3 * (n - 1) + 1 := by omega
      have hexp : 3 * n - 3 = 3 * (n - 1) := by omega
      have hscale : alpha u v ^ (3 * n - 2) =
          2 ^ (3 * n - 3) * (alpha u v * z ^ (n - 1)) := by
        rw [hindex, pow_succ', hblock, hexp]
        ring
      have hod := odd_mul hvo (alpha u v) (z ^ (n - 1)) huo (by simp [alpha])
        (hnorm (n - 1))
      exact finish _ (by omega) _ _ hscale (Or.inl (Int.two_dvd_ne_zero.mpr hod.1))
    · have hindex : 3 * n - 1 = 2 + 3 * (n - 1) := by omega
      have hexp : 3 * n - 2 = 3 * (n - 1) + 1 := by omega
      have hscale : alpha u v ^ (3 * n - 1) =
          2 ^ (3 * n - 2) * (w * z ^ (n - 1)) := by
        rw [hindex, pow_add, hw, hblock, hexp, pow_succ]
        ring
      have hod := odd_mul hvo w (z ^ (n - 1)) hwr huo (hnorm (n - 1))
      exact finish _ (by omega) _ _ hscale (Or.inl (Int.two_dvd_ne_zero.mpr hod.1))
    · exact finish _ (by omega) _ _ (hblock n) (odd_norm_not_both _ (hnorm n))
  · intro hd n hn
    obtain ⟨huo, _⟩ := odd_uv huv (by omega)
    obtain ⟨t, ht⟩ : ∃ t : ℤ, (u : ℤ) ^ 2 - v = 8 * t :=
      ⟨((u : ℤ) ^ 2 - v) / 8, by omega⟩
    obtain ⟨z, hz, hr, _, _⟩ := repeated_halving t huo ht (n - 1)
    have hindex : n - 1 + 1 = n := by omega
    rw [hindex] at hz
    exact finish _ hn z _ hz (Or.inl (Int.two_dvd_ne_zero.mpr hr))

end

end MetaMathlibExt

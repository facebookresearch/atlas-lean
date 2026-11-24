/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_fermatLastTheoremFive.lean`
and
`P2M/Sol/S_fermatLastTheoremFive.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.NumberTheory.FLT.Basic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.QuadraticForms.GoldenOrderEquiv

/-!
# Fermat's Last Theorem for exponent 5

This file proves `fermatLastTheoremFive : FermatLastTheoremFor 5`.

The proof works in `QuadraticAlgebra ℤ 1 1`, the ring `ℤ[φ]` with `φ ^ 2 = φ + 1`, where
`φ = (1 + √5) / 2`. A norm-Euclidean division makes this ring a Euclidean domain, hence a
unique factorization domain. Its units are `± φ ^ n`, and a unit congruent to an integer
modulo `5` is a fifth power. With these facts:

* the first case (`5` divides none of `x`, `y`, `z`) follows from a computation in
  `ZMod 25`;
* the second case, with `5` dividing the even variable or an odd variable, is refuted by
  two infinite descents. Each descent step factors `a ^ 2 - 5 * b ^ 2 = w ^ 5` (or `4 * w ^ 5`)
  over `ℤ[φ]` as a fifth power and produces a smaller solution of the same shape.

All auxiliary definitions and lemmas are private.
-/

@[expose] public section

namespace FermatLastTheoremFive

/-- The ring `ℤ[φ]`, `φ = (1 + √5) / 2`, as Mathlib's quadratic algebra. -/
private abbrev Zphi := QuadraticAlgebra ℤ 1 1

namespace Zphi

@[scoped simp] private theorem re_zero : (0 : Zphi).re = 0 := rfl
@[scoped simp] private theorem im_zero : (0 : Zphi).im = 0 := rfl
@[scoped simp] private theorem re_one : (1 : Zphi).re = 1 := rfl
@[scoped simp] private theorem im_one : (1 : Zphi).im = 0 := rfl
@[scoped simp] private theorem re_mul (z w : Zphi) :
    (z * w).re = z.re * w.re + z.im * w.im := by simp
@[scoped simp] private theorem im_mul (z w : Zphi) :
    (z * w).im = z.re * w.im + z.im * w.re + z.im * w.im := by simp
@[scoped simp] private theorem re_sub (z w : Zphi) : (z - w).re = z.re - w.re := rfl
@[scoped simp] private theorem im_sub (z w : Zphi) : (z - w).im = z.im - w.im := rfl
@[scoped simp] private theorem re_ofNat (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : Zphi).re = OfNat.ofNat n := rfl
@[scoped simp] private theorem im_ofNat (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : Zphi).im = 0 := rfl

private def phi : Zphi := ⟨0, 1⟩

@[scoped simp] private theorem re_phi : phi.re = 0 := rfl
@[scoped simp] private theorem im_phi : phi.im = 1 := rfl

private def sqrt5 : Zphi := ⟨-1, 2⟩

@[scoped simp] private theorem re_sqrt5 : sqrt5.re = -1 := rfl
@[scoped simp] private theorem im_sqrt5 : sqrt5.im = 2 := rfl

@[scoped simp] private theorem sqrt5_sq : sqrt5 * sqrt5 = 5 := by ext <;> simp

private def conj : Zphi →+* Zphi where
  toFun z := ⟨z.re + z.im, -z.im⟩
  map_zero' := by ext <;> simp
  map_add' _ _ := by ext <;> simp <;> ring
  map_one' := by ext <;> simp
  map_mul' _ _ := by ext <;> simp <;> ring

@[scoped simp] private theorem re_conj (z : Zphi) : (conj z).re = z.re + z.im := rfl
@[scoped simp] private theorem im_conj (z : Zphi) : (conj z).im = -z.im := rfl

@[scoped simp] private theorem conj_mk (a b : ℤ) : conj ⟨a, b⟩ = ⟨a + b, -b⟩ := rfl

@[scoped simp] private theorem conj_conj (z : Zphi) : conj (conj z) = z := by
  ext <;> simp

@[scoped simp] private theorem conj_intCast (n : ℤ) : conj (n : Zphi) = n := by
  ext <;> simp

private def norm (z : Zphi) : ℤ := z.re * z.re + z.re * z.im - z.im * z.im

@[scoped simp] private theorem norm_mk (a b : ℤ) :
    norm ⟨a, b⟩ = a * a + a * b - b * b := rfl

private theorem mul_conj (z : Zphi) : z * conj z = (norm z : Zphi) := by
  ext <;> (simp [norm]; try ring)

@[scoped simp] private theorem norm_zero : norm 0 = 0 := by simp [norm]
@[scoped simp] private theorem norm_one : norm 1 = 1 := by simp [norm]
@[scoped simp] private theorem norm_intCast (n : ℤ) : norm (n : Zphi) = n * n := by
  simp [norm]
@[scoped simp] private theorem norm_phi : norm phi = -1 := by simp [norm]
@[scoped simp] private theorem norm_sqrt5 : norm sqrt5 = -5 := by simp [norm]

private theorem norm_mul (z w : Zphi) : norm (z * w) = norm z * norm w := by
  simp [norm]; ring

private theorem sq_ne_five_mul_sq (x y : ℤ) (hy : y ≠ 0) : x ^ 2 ≠ 5 * y ^ 2 := by
  induction hn : y.natAbs using Nat.strong_induction_on generalizing x y with
  | _ n ih =>
    intro hxy
    have h5 : Prime (5 : ℤ) := by norm_num
    obtain ⟨x1, hx1⟩ : (5 : ℤ) ∣ x := h5.dvd_of_dvd_pow (n := 2) ⟨y ^ 2, hxy⟩
    rw [hx1] at hxy
    ring_nf at hxy
    have hy2 : y ^ 2 = 5 * x1 ^ 2 := by nlinarith [hxy]
    obtain ⟨y1, hy1⟩ : (5 : ℤ) ∣ y := h5.dvd_of_dvd_pow (n := 2) ⟨x1 ^ 2, hy2⟩
    rw [hy1] at hy2
    ring_nf at hy2
    have hx2 : x1 ^ 2 = 5 * y1 ^ 2 := by nlinarith [hy2]
    have hy10 : y1 ≠ 0 := fun h => hy (by simp [hy1, h])
    have hlt : y1.natAbs < n := by
      have h5y : y.natAbs = 5 * y1.natAbs := by rw [hy1, Int.natAbs_mul]; rfl
      have : y1.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hy10
      omega
    exact ih y1.natAbs hlt x1 y1 hy10 rfl hx2

private theorem norm_eq_zero_iff {z : Zphi} : norm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have key : (2 * z.re + z.im) ^ 2 = 5 * z.im ^ 2 := by
      simp [norm] at h; nlinarith [h]
    have him : z.im = 0 := by
      by_contra hb
      exact sq_ne_five_mul_sq (2 * z.re + z.im) z.im hb key
    refine QuadraticAlgebra.ext ?_ him
    simpa [norm, him, mul_self_eq_zero] using h
  · rintro rfl; simp

private theorem norm_ne_zero_iff {z : Zphi} : norm z ≠ 0 ↔ z ≠ 0 := norm_eq_zero_iff.not

private scoped instance : IsDomain Zphi := by
  refine (isDomain_iff_noZeroDivisors_and_nontrivial _).mpr
    ⟨⟨fun {a b} hab => ?_⟩, inferInstance⟩
  by_contra h
  push Not at h
  obtain ⟨ha, hb⟩ := h
  have : norm a * norm b = 0 := by rw [← norm_mul, hab, norm_zero]
  rcases mul_eq_zero.mp this with h | h
  · exact ha (norm_eq_zero_iff.mp h)
  · exact hb (norm_eq_zero_iff.mp h)

end Zphi

end FermatLastTheoremFive

namespace FermatLastTheoremFive

namespace Zphi

private def ofPair (a b : ℤ) : Zphi := ⟨a - b, 2 * b⟩

@[scoped simp] private theorem re_ofPair (a b : ℤ) : (ofPair a b).re = a - b := rfl
@[scoped simp] private theorem im_ofPair (a b : ℤ) : (ofPair a b).im = 2 * b := rfl

private theorem ofPair_eq (a b : ℤ) : ofPair a b = a + b * sqrt5 := by
  ext <;> simp [ofPair, sqrt5] <;> ring

@[scoped simp] private theorem norm_ofPair (a b : ℤ) : norm (ofPair a b) = a ^ 2 - 5 * b ^ 2 := by
  simp [ofPair, norm]; ring

private theorem conj_ofPair (a b : ℤ) : conj (ofPair a b) = ofPair a (-b) := by
  (ext <;> simp [ofPair]); ring

private def sA (z : Zphi) : ℤ := 2 * z.re + z.im

private def sB (z : Zphi) : ℤ := z.im

private theorem two_mul_eq_ofPair (z : Zphi) : 2 * z = ofPair (sA z) (sB z) := by
  ext <;> simp [ofPair, sA, sB]

private theorem sA_conj (z : Zphi) : sA (conj z) = sA z := by simp [sA]; ring
private theorem sB_conj (z : Zphi) : sB (conj z) = -sB z := by simp [sB]

private theorem four_mul_norm (z : Zphi) : 4 * norm z = (sA z) ^ 2 - 5 * (sB z) ^ 2 := by
  simp [norm, sA, sB]; ring

private theorem sA_parity (z : Zphi) : sA z ≡ sB z [ZMOD 2] := by
  change (2 * z.re + z.im) % 2 = z.im % 2
  omega

private theorem eq_ofPair_iff_even_im (z : Zphi) :
    (∃ a b : ℤ, z = ofPair a b) ↔ Even z.im := by
  constructor
  · rintro ⟨a, b, rfl⟩; exact ⟨b, by simp [ofPair]; ring⟩
  · rintro ⟨b, hb⟩
    exact ⟨z.re + b, b, by (ext <;> simp [ofPair]); omega⟩

private theorem five_dvd_iff (z : Zphi) :
    (5 : Zphi) ∣ z ↔ (5 : ℤ) ∣ z.re ∧ (5 : ℤ) ∣ z.im := by
  constructor
  · rintro ⟨w, rfl⟩
    constructor
    · exact ⟨w.re, by simp⟩
    · exact ⟨w.im, by simp⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    exact ⟨⟨u, v⟩, by ext <;> simp [hu, hv]⟩

private theorem two_dvd_iff (z : Zphi) :
    (2 : Zphi) ∣ z ↔ (2 : ℤ) ∣ z.re ∧ (2 : ℤ) ∣ z.im := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨⟨w.re, by simp⟩, ⟨w.im, by simp⟩⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    exact ⟨⟨u, v⟩, by ext <;> simp [hu, hv]⟩

private theorem sqrt5_dvd_iff (z : Zphi) :
    sqrt5 ∣ z ↔ (5 : ℤ) ∣ (z.re + 3 * z.im) := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.re + w.im, by simp; ring⟩
  · rintro ⟨k, hk⟩
    exact ⟨⟨z.im - k, 2 * k - z.im⟩, by ext <;> simp <;> omega⟩

private theorem prime_sqrt5 : Prime sqrt5 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := congrArg QuadraticAlgebra.im h
    simp at this
  · rintro ⟨u, hu⟩
    have h1 : sqrt5 ∣ 1 := hu ▸ ⟨↑u⁻¹, by simp [← Units.val_mul]⟩
    obtain ⟨w, hw⟩ := h1
    have := congrArg norm hw
    rw [norm_mul] at this
    simp at this
    omega
  · intro a b h
    rw [sqrt5_dvd_iff] at h
    rw [sqrt5_dvd_iff, sqrt5_dvd_iff]
    have h5 : Prime (5 : ℤ) := by norm_num
    have key : (5 : ℤ) ∣ (a.re + 3 * a.im) * (b.re + 3 * b.im) := by
      obtain ⟨k, hk⟩ := h
      simp only [QuadraticAlgebra.re_mul, one_mul, QuadraticAlgebra.im_mul] at hk
      exact ⟨k + a.im * b.im, by linear_combination hk⟩
    exact h5.dvd_mul.mp key

private theorem no_norm_two (z : Zphi) : norm z ≠ 2 ∧ norm z ≠ -2 := by
  have hsq : ∀ x : ZMod 5, x ^ 2 ≠ 3 ∧ x ^ 2 ≠ 2 := by decide
  have h4 : (2 * z.re + z.im) ^ 2 = 4 * norm z + 5 * z.im ^ 2 := by
    simp [norm]; ring
  have h5 : (5 : ZMod 5) = 0 := by decide
  constructor <;> intro h <;> rw [h] at h4
  · refine (hsq ((2 * z.re + z.im : ℤ) : ZMod 5)).1 ?_
    have := congrArg (Int.cast : ℤ → ZMod 5) h4
    push_cast at this ⊢
    rw [this, h5]
    ring_nf
    decide
  · refine (hsq ((2 * z.re + z.im : ℤ) : ZMod 5)).2 ?_
    have := congrArg (Int.cast : ℤ → ZMod 5) h4
    push_cast at this ⊢
    rw [this, h5]
    ring_nf
    decide

private theorem prime_two : Prime (2 : Zphi) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := congrArg QuadraticAlgebra.re h
    simp at this
  · rintro ⟨u, hu⟩
    have h1 : (2 : Zphi) ∣ 1 := hu ▸ ⟨↑u⁻¹, by simp [← Units.val_mul]⟩
    obtain ⟨w, hw⟩ := h1
    have := congrArg norm hw
    rw [norm_mul] at this
    simp [norm] at this
    omega
  · intro a b h
    rw [two_dvd_iff] at h
    rw [two_dvd_iff, two_dvd_iff]
    simp only [re_mul, im_mul] at h
    obtain ⟨h1, h2⟩ := h
    have key : ∀ x y u v : ZMod 2, x * u + y * v = 0 →
        x * v + y * u + y * v = 0 →
        (x = 0 ∧ y = 0) ∨ (u = 0 ∧ v = 0) := by decide
    have c1 : ((a.re * b.re + a.im * b.im : ℤ) : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr h1
    have c2 : ((a.re * b.im + a.im * b.re + a.im * b.im : ℤ) : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr h2
    push_cast at c1 c2
    rcases key (a.re : ZMod 2) (a.im : ZMod 2) (b.re : ZMod 2) (b.im : ZMod 2)
        c1 c2 with ⟨hx, hy⟩ | ⟨hu, hv⟩
    · exact Or.inl ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hx,
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hy⟩
    · exact Or.inr ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hu,
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hv⟩

private theorem sA_pow_five (z : Zphi) :
    16 * sA (z ^ 5) =
      sA z * ((sA z) ^ 4 + 50 * (sA z) ^ 2 * (sB z) ^ 2 + 125 * (sB z) ^ 4) := by
  simp [sA, sB, pow_succ]; ring

private theorem sB_pow_five (z : Zphi) :
    16 * sB (z ^ 5) =
      5 * sB z * ((sA z) ^ 4 + 10 * (sA z) ^ 2 * (sB z) ^ 2 + 5 * (sB z) ^ 4) := by
  simp [sA, sB, pow_succ]; ring

private theorem pow_five_congr_int (z : Zphi) :
    ∃ m : ℤ, (5 : Zphi) ∣ (z ^ 5 - (m : Zphi)) := by
  refine ⟨z.re ^ 5 + 3 * z.im ^ 5,
    ⟨⟨2 * z.re ^ 3 * z.im ^ 2 + 2 * z.re ^ 2 * z.im ^ 3 + 2 * z.re * z.im ^ 4,
      z.re ^ 4 * z.im + 2 * z.re ^ 3 * z.im ^ 2 + 4 * z.re ^ 2 * z.im ^ 3 +
        3 * z.re * z.im ^ 4 + z.im ^ 5⟩, ?_⟩⟩
  ext <;> simp [pow_succ] <;> ring

end Zphi

end FermatLastTheoremFive

namespace FermatLastTheoremFive

namespace Zphi

private def roundDiv (p q : ℤ) : ℤ := Int.fdiv (2 * p + q) (2 * q)

private theorem abs_roundDiv_sub_le (p q : ℤ) (hq : q ≠ 0) :
    2 * |p - q * roundDiv p q| ≤ |q| := by
  have key : ∀ p q : ℤ, 0 < q → 2 * |p - q * roundDiv p q| ≤ |q| := by
    intro p q hq
    have hd := Int.mul_fdiv_add_fmod (2 * p + q) (2 * q)
    have h1 : 0 ≤ (2 * p + q).fmod (2 * q) := Int.fmod_nonneg_of_pos _ (by linarith)
    have h2 : (2 * p + q).fmod (2 * q) < 2 * q := Int.fmod_lt_of_pos _ (by linarith)
    have h2x : (2 : ℤ) * |p - q * roundDiv p q| = |2 * (p - q * roundDiv p q)| := by
      rw [abs_mul]; norm_num
    rw [h2x, roundDiv, abs_of_pos hq, abs_le]
    constructor <;> nlinarith [hd, h1, h2]
  rcases lt_or_gt_of_ne hq with hq' | hq'
  · have h := key (-p) (-q) (by linarith)
    rw [roundDiv] at h ⊢
    have hfd : (2 * -p + -q).fdiv (2 * -q) = (2 * p + q).fdiv (2 * q) := by
      rw [show 2 * -p + -q = -(2 * p + q) by ring, show 2 * -q = -(2 * q) by ring,
        Int.neg_fdiv_neg]
    rw [hfd] at h
    calc 2 * |p - q * (2 * p + q).fdiv (2 * q)|
        = 2 * |-p - -q * (2 * p + q).fdiv (2 * q)| := by rw [← abs_neg]; ring_nf
      _ ≤ |-q| := h
      _ = |q| := abs_neg q
  · exact key p q hq'

private scoped instance : Div Zphi :=
  ⟨fun a b =>
    let c := a * conj b
    let n := norm b
    ⟨roundDiv c.re n, roundDiv c.im n⟩⟩

private theorem div_def (a b : Zphi) :
    a / b = ⟨roundDiv (a * conj b).re (norm b), roundDiv (a * conj b).im (norm b)⟩ := rfl

private scoped instance : Mod Zphi := ⟨fun a b => a - b * (a / b)⟩

private theorem mod_def (a b : Zphi) : a % b = a - b * (a / b) := rfl

@[scoped simp] private theorem div_zero' (a : Zphi) : a / 0 = 0 := by
  ext <;> simp [div_def, roundDiv, Int.fdiv]

private theorem quotient_mul_add_remainder (a b : Zphi) : b * (a / b) + a % b = a := by
  rw [mod_def]; ring

private theorem natAbs_norm_mod_lt (a b : Zphi) (hb : b ≠ 0) :
    (norm (a % b)).natAbs < (norm b).natAbs := by
  have hn : norm b ≠ 0 := norm_ne_zero_iff.mpr hb
  have final : ∀ N R e1 e2 : ℤ, N ≠ 0 → 2 * |e1| ≤ |N| → 2 * |e2| ≤ |N| →
      R * N = e1 ^ 2 + e1 * e2 - e2 ^ 2 → R.natAbs < N.natAbs := by
    intro N R e1 e2 hN h1 h2 hRN
    have hs1 : 4 * e1 ^ 2 ≤ N ^ 2 := by
      nlinarith [abs_nonneg e1, abs_nonneg N, sq_abs e1, sq_abs N]
    have hs2 : 4 * e2 ^ 2 ≤ N ^ 2 := by
      nlinarith [abs_nonneg e2, abs_nonneg N, sq_abs e2, sq_abs N]
    have hup : 16 * (R * N) ≤ 5 * N ^ 2 := by
      rw [hRN]; nlinarith [sq_nonneg (e1 - 2 * e2), hs1]
    have hlo : -(5 * N ^ 2) ≤ 16 * (R * N) := by
      rw [hRN]; nlinarith [sq_nonneg (2 * e1 + e2), hs2]
    have habs : 16 * |R| * |N| ≤ 5 * |N| * |N| := by
      have h16 : |16 * (R * N)| ≤ 5 * N ^ 2 := abs_le.mpr ⟨hlo, hup⟩
      calc 16 * |R| * |N| = |16 * (R * N)| := by
            rw [abs_mul, abs_mul]; norm_num; ring
        _ ≤ 5 * N ^ 2 := h16
        _ = 5 * |N| * |N| := by rw [mul_assoc, abs_mul_abs_self]; ring
    have hNpos : 0 < |N| := abs_pos.mpr hN
    have hR : 16 * |R| ≤ 5 * |N| := _root_.le_of_mul_le_mul_right habs hNpos
    have hlt : |R| < |N| := by linarith
    rw [← @Nat.cast_lt ℤ, Int.natCast_natAbs, Int.natCast_natAbs]
    exact hlt
  have hid : ∀ q1 q2 : ℤ,
      norm (a - b * ⟨q1, q2⟩) * norm b =
        ((a * conj b).re - norm b * q1) ^ 2
        + ((a * conj b).re - norm b * q1) * ((a * conj b).im - norm b * q2)
        - ((a * conj b).im - norm b * q2) ^ 2 := by
    intro q1 q2
    simp only [show ∀ z : Zphi, norm z = z.re * z.re + z.re * z.im - z.im * z.im
        from fun _ => rfl,
      re_sub, im_sub, re_mul, im_mul, re_conj, im_conj]
    ring
  have hstar : norm (a % b) * norm b =
      ((a * conj b).re - norm b * roundDiv (a * conj b).re (norm b)) ^ 2
      + ((a * conj b).re - norm b * roundDiv (a * conj b).re (norm b))
        * ((a * conj b).im - norm b * roundDiv (a * conj b).im (norm b))
      - ((a * conj b).im - norm b * roundDiv (a * conj b).im (norm b)) ^ 2 := by
    rw [mod_def, div_def]; exact hid _ _
  exact final (norm b) (norm (a % b)) _ _ hn
    (abs_roundDiv_sub_le _ _ hn) (abs_roundDiv_sub_le _ _ hn) hstar

private theorem natAbs_norm_le_natAbs_norm_mul (a b : Zphi) (hb : b ≠ 0) :
    (norm a).natAbs ≤ (norm (a * b)).natAbs := by
  rw [norm_mul, Int.natAbs_mul]
  have : (norm b).natAbs ≠ 0 := by
    simpa [Int.natAbs_ne_zero] using norm_ne_zero_iff.mpr hb
  exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero this)

private scoped instance : EuclideanDomain Zphi :=
  { (inferInstance : CommRing Zphi), (inferInstance : Nontrivial Zphi) with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := div_zero'
    quotient_mul_add_remainder_eq := quotient_mul_add_remainder
    r := InvImage (· < ·) (fun z => (norm z).natAbs)
    r_wellFounded := InvImage.wf _ Nat.lt_wfRel.wf
    remainder_lt := fun a b hb => natAbs_norm_mod_lt a b hb
    mul_left_not_lt := fun a b hb h =>
      absurd h (not_lt_of_ge (natAbs_norm_le_natAbs_norm_mul a b hb)) }

end Zphi

end FermatLastTheoremFive

namespace FermatLastTheoremFive

namespace Zphi

private theorem phi_mul_phi_sub_one : phi * (phi - 1) = 1 := by
  ext <;> simp [phi]

private theorem isUnit_phi : IsUnit phi :=
  ⟨⟨phi, phi - 1, phi_mul_phi_sub_one, by
    rw [mul_comm]; exact phi_mul_phi_sub_one⟩, rfl⟩

private theorem phi_pow_succ_coords (n : ℕ) :
    phi ^ (n + 1) = ⟨(Nat.fib n : ℤ), (Nat.fib (n + 1) : ℤ)⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ k ih =>
    rw [pow_succ, ih]
    ext <;> simp [Nat.fib_add_two]

private theorem fib_five_dvd_iff (n : ℕ) : (5 : ℕ) ∣ Nat.fib n ↔ 5 ∣ n := by
  have hfib5 : Nat.fib 5 = 5 := rfl
  have h : Nat.fib (Nat.gcd 5 n) = Nat.gcd 5 (Nat.fib n) := by
    simpa [hfib5] using Nat.fib_gcd 5 n
  constructor
  · intro h5
    rw [Nat.gcd_eq_left h5] at h
    have hd : Nat.gcd 5 n ∣ 5 := Nat.gcd_dvd_left 5 n
    rcases (by norm_num : Nat.Prime 5).eq_one_or_self_of_dvd _ hd with h1 | h1
    · rw [h1] at h; simp at h
    · exact h1 ▸ Nat.gcd_dvd_right 5 n
  · intro h5
    rw [Nat.gcd_eq_left h5, hfib5] at h
    exact h ▸ Nat.gcd_dvd_right 5 (Nat.fib n)

private theorem isUnit_phi_sub_one : IsUnit (phi - 1) :=
  ⟨⟨phi - 1, phi, by rw [mul_comm]; exact phi_mul_phi_sub_one,
    phi_mul_phi_sub_one⟩, rfl⟩

private theorem im_phi_pow (n : ℕ) : (phi ^ n).im = (Nat.fib n : ℤ) := by
  cases n with
  | zero => simp
  | succ k => rw [phi_pow_succ_coords]

private theorem phi_sub_one_pow_coords (n : ℕ) :
    (phi - 1) ^ n = ⟨(-1)^n * (Nat.fib (n+1) : ℤ), (-1)^(n+1) * (Nat.fib n : ℤ)⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ k ih =>
    rw [pow_succ, ih]
    ext <;> (simp [Nat.fib_add_two, pow_succ]; try ring)

private theorem exists_phi_pow_of_isUnit (z : Zphi) (hz : IsUnit z) :
    ∃ n : ℕ, z = phi ^ n ∨ z = -(phi ^ n) ∨ z * phi ^ n = 1 ∨ z * phi ^ n = -1 :=
  QuadraticAlgebra.exists_omega_pow_of_isUnit z hz

private theorem eq_pow_five_of_isUnit_of_congruent (u : Zphi) (hu : IsUnit u)
    (m : ℤ) (hm : (5 : Zphi) ∣ (u - (m : Zphi))) :
    ∃ v : Zphi, IsUnit v ∧ u = v ^ 5 := by
  obtain ⟨c, hc⟩ := hm
  have h5im : (5 : ℤ) ∣ u.im := ⟨c.im, by simpa using congrArg QuadraticAlgebra.im hc⟩
  obtain ⟨n, hn | hn | hn | hn⟩ := exists_phi_pow_of_isUnit u hu
  · have h5fib : (5 : ℕ) ∣ Nat.fib n := by
      have h1 : (5 : ℤ) ∣ (Nat.fib n : ℤ) := by rw [← im_phi_pow, ← hn]; exact h5im
      exact_mod_cast h1
    obtain ⟨k, rfl⟩ := (fib_five_dvd_iff n).mp h5fib
    exact ⟨phi ^ k, isUnit_phi.pow k, by rw [hn, ← pow_mul, mul_comm k 5]⟩
  · have h5fib : (5 : ℕ) ∣ Nat.fib n := by
      have h1 : (5 : ℤ) ∣ -(Nat.fib n : ℤ) := by
        rw [← im_phi_pow]
        simpa [hn] using h5im
      have h2 := (dvd_neg).mp h1
      exact_mod_cast h2
    obtain ⟨k, rfl⟩ := (fib_five_dvd_iff n).mp h5fib
    refine ⟨-(phi ^ k), (isUnit_phi.pow k).neg, ?_⟩
    rw [hn, Odd.neg_pow (by norm_num : Odd 5), ← pow_mul, mul_comm k 5]
  · have hu_eq : u = (phi - 1) ^ n := by
      have hinv : phi ^ n * (phi - 1) ^ n = 1 := by
        rw [← mul_pow, phi_mul_phi_sub_one, one_pow]
      calc u = u * (phi ^ n * (phi - 1) ^ n) := by rw [hinv, mul_one]
        _ = (u * phi ^ n) * (phi - 1) ^ n := by ring
        _ = (phi - 1) ^ n := by rw [hn, one_mul]
    have h5fib : (5 : ℕ) ∣ Nat.fib n := by
      have h2 : (5 : ℤ) ∣ (-1)^(n+1) * (Nat.fib n : ℤ) := by
        have h : u.im = (-1)^(n+1) * (Nat.fib n : ℤ) := by
          rw [hu_eq, phi_sub_one_pow_coords]
        rwa [h] at h5im
      have h3 := Int.natAbs_dvd_natAbs.mpr h2
      simpa [Int.natAbs_mul, Int.natAbs_pow] using h3
    obtain ⟨k, rfl⟩ := (fib_five_dvd_iff n).mp h5fib
    exact ⟨(phi - 1) ^ k, isUnit_phi_sub_one.pow k,
      by rw [hu_eq, ← pow_mul, mul_comm k 5]⟩
  · have hu_eq : u = -((phi - 1) ^ n) := by
      have hinv : phi ^ n * (phi - 1) ^ n = 1 := by
        rw [← mul_pow, phi_mul_phi_sub_one, one_pow]
      calc u = u * (phi ^ n * (phi - 1) ^ n) := by rw [hinv, mul_one]
        _ = (u * phi ^ n) * (phi - 1) ^ n := by ring
        _ = -((phi - 1) ^ n) := by rw [hn]; ring
    have h5fib : (5 : ℕ) ∣ Nat.fib n := by
      have h2 : (5 : ℤ) ∣ -((-1)^(n+1) * (Nat.fib n : ℤ)) := by
        have h : u.im = -((-1)^(n+1) * (Nat.fib n : ℤ)) := by
          rw [hu_eq, phi_sub_one_pow_coords]; simp
        rwa [h] at h5im
      have h3 := Int.natAbs_dvd_natAbs.mpr h2
      simpa [Int.natAbs_mul, Int.natAbs_pow] using h3
    obtain ⟨k, rfl⟩ := (fib_five_dvd_iff n).mp h5fib
    refine ⟨-((phi - 1) ^ k), (isUnit_phi_sub_one.pow k).neg, ?_⟩
    rw [hu_eq, Odd.neg_pow (by norm_num : Odd 5), ← pow_mul, mul_comm k 5]

end Zphi

end FermatLastTheoremFive

namespace FermatLastTheoremFive

private def IsFifthPower (n : ℤ) : Prop := ∃ m : ℤ, n = m ^ 5

private theorem IsFifthPower.neg {n : ℤ} : IsFifthPower n → IsFifthPower (-n) :=
  fun ⟨m, hm⟩ => ⟨-m, by rw [hm]; ring⟩

private theorem isFifthPower_pow_five (m : ℤ) : IsFifthPower (m ^ 5) := ⟨m, rfl⟩

private theorem pow_five_add_pow_five_sub (p q : ℤ) :
    (p + q) ^ 5 + (p - q) ^ 5 = 2 * p * (p ^ 4 + 10 * p ^ 2 * q ^ 2 + 5 * q ^ 4) := by
  ring

private theorem quartic_eq_sq_sub_five_sq (q r : ℤ) :
    q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4 =
      (q ^ 2 + 25 * r ^ 2) ^ 2 - 5 * (10 * r ^ 2) ^ 2 := by
  ring

private theorem quartic_eq_sq_sub_five_sq' (c d : ℤ) :
    c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4 =
      (c ^ 2 + 5 * d ^ 2) ^ 2 - 5 * (2 * d ^ 2) ^ 2 := by
  ring

private theorem quartic_pos {c : ℤ} (d : ℤ) (hc : c ≠ 0) :
    0 < c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4 := by
  have h1 : 0 < c ^ 4 := by positivity
  nlinarith [sq_nonneg (c * d), sq_nonneg (d ^ 2)]

private theorem int_pow_of_coprime_of_mul_eq_pow {a b c : ℤ} (hab : IsCoprime a b)
    (h : a * b = c ^ 5) : IsFifthPower a := by
  have hu : IsUnit (gcd a b) := hab.isUnit_of_dvd' (gcd_dvd_left a b) (gcd_dvd_right a b)
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow hu h
  rcases Int.associated_iff.mp hd with h1 | h1
  · exact ⟨d, h1.symm⟩
  · exact ⟨-d, by rw [← neg_neg a, ← h1]; ring⟩

private theorem int_pow_pow_of_coprime_of_mul_eq_pow {a b c : ℤ} (hab : IsCoprime a b)
    (h : a * b = c ^ 5) : IsFifthPower a ∧ IsFifthPower b :=
  ⟨int_pow_of_coprime_of_mul_eq_pow hab h,
   int_pow_of_coprime_of_mul_eq_pow hab.symm (by rwa [mul_comm] at h)⟩

private theorem odd_pow_four_mod_32 {n : ℤ} (hn : Odd n) :
    n ^ 4 % 32 = 1 ∨ n ^ 4 % 32 = 17 := by
  have key : ∀ r : ℤ, 0 ≤ r → r < 32 → r % 2 = 1 →
      r ^ 4 % 32 = 1 ∨ r ^ 4 % 32 = 17 := by
    intro r h0 h32 hodd
    interval_cases r <;> simp_all
  rw [← Int.ModEq.pow 4 (Int.emod_emod_of_dvd n dvd_rfl)]
  exact key _ (Int.emod_nonneg n (by norm_num)) (Int.emod_lt_of_pos n (by norm_num))
    (by rw [Int.emod_emod_of_dvd n (by norm_num : (2 : ℤ) ∣ 32)]; exact Int.odd_iff.mp hn)

private theorem quartic_mod_32 {h k : ℤ} (hh : Odd h) (hk : Odd k) :
    (h ^ 4 + 10 * h ^ 2 * k ^ 2 + 5 * k ^ 4) % 32 = 16 := by
  obtain ⟨a, ha⟩ := hh
  obtain ⟨b, hb⟩ := hk
  have key : ∀ x y : ZMod 32,
      (2*x+1) ^ 4 + 10 * (2*x+1) ^ 2 * (2*y+1) ^ 2 + 5 * (2*y+1) ^ 4 = 16 := by decide
  have hz : ((h ^ 4 + 10 * h ^ 2 * k ^ 2 + 5 * k ^ 4 : ℤ) : ZMod 32) = ((16 : ℤ) : ZMod 32) := by
    push_cast [ha, hb]
    exact key (a : ZMod 32) (b : ZMod 32)
  have hmod := (ZMod.intCast_eq_intCast_iff' _ _ _).mp hz
  simpa using hmod

end FermatLastTheoremFive

namespace FermatLastTheoremFive

namespace Zphi

attribute [local instance] UniqueFactorizationMonoid.toGCDMonoid

private theorem isCoprime_conj_int {a b : ℤ} (hab : IsCoprime a b) (ha : Odd a)
    (hb : Even b) (h5 : ¬(5 : ℤ) ∣ a) :
    IsCoprime (ofPair a b) (conj (ofPair a b)) := by
  have h5' : Prime (5 : ℤ) := by norm_num
  have ha5 : IsCoprime a (5 : ℤ) := ((Prime.coprime_iff_not_dvd h5').mpr h5).symm
  obtain ⟨u, v, huv⟩ := ha5.mul_right hab
  have hNodd : Odd (a ^ 2 - 5 * b ^ 2) := by
    obtain ⟨m, rfl⟩ := ha
    obtain ⟨r, rfl⟩ := hb
    exact ⟨2 * m ^ 2 + 2 * m - 10 * r ^ 2, by ring⟩
  obtain ⟨k, hk⟩ := hNodd
  have h2N : IsCoprime (2 : ℤ) (a ^ 2 - 5 * b ^ 2) := ⟨-k, 1, by rw [hk]; ring⟩
  obtain ⟨s, t, hst⟩ := h2N
  set ξ := ofPair a b with hξ
  have hsum : ξ + conj ξ = ((2 * a : ℤ) : Zphi) := by
    (ext <;> simp [ofPair, hξ]); ring
  have hdiff : ξ - conj ξ = ((2 * b : ℤ) : Zphi) * sqrt5 := by
    (ext <;> simp [ofPair, sqrt5, hξ]); ring
  have hmc : ξ * conj ξ = ((a ^ 2 - 5 * b ^ 2 : ℤ) : Zphi) := by
    rw [mul_conj, norm_ofPair]
  set p : Zphi := (u : Zphi) + (v : Zphi) * sqrt5 with hp
  set q : Zphi := (u : Zphi) - (v : Zphi) * sqrt5 with hq
  have hcomb : p * ξ + q * conj ξ = ((2 : ℤ) : Zphi) := by
    have e1 : p * ξ + q * conj ξ
        = (u : Zphi) * (ξ + conj ξ) + (v : Zphi) * (ξ - conj ξ) * sqrt5 := by
      rw [hp, hq]; ring
    rw [e1, hsum, hdiff]
    have e2 : (u : Zphi) * ((2*a : ℤ) : Zphi) + (v : Zphi) * (((2*b : ℤ) : Zphi) * sqrt5) * sqrt5
        = (u : Zphi) * ((2*a : ℤ) : Zphi) + (v : Zphi) * ((2*b : ℤ) : Zphi) * (sqrt5 * sqrt5) := by
          ring
    rw [e2, sqrt5_sq]
    have huv2 : ((2 * (u * a + v * (5 * b)) : ℤ) : Zphi) = ((2 : ℤ) : Zphi) := by
      rw [huv]; norm_num
    calc (u : Zphi) * ((2*a : ℤ) : Zphi) + (v : Zphi) * ((2*b : ℤ) : Zphi) * 5
        = ((2 * (u * a + v * (5 * b)) : ℤ) : Zphi) := by push_cast; ring
      _ = ((2 : ℤ) : Zphi) := huv2
  refine ⟨(s : Zphi) * p, (s : Zphi) * q + (t : Zphi) * ξ, ?_⟩
  have hst' : ((s * 2 + t * (a ^ 2 - 5 * b ^ 2) : ℤ) : Zphi) = 1 := by
    rw [hst]; norm_num
  calc (s : Zphi) * p * ξ + ((s : Zphi) * q + (t : Zphi) * ξ) * conj ξ
      = (s : Zphi) * (p * ξ + q * conj ξ) + (t : Zphi) * (ξ * conj ξ) := by ring
    _ = (s : Zphi) * ((2 : ℤ) : Zphi) + (t : Zphi) * ((a ^ 2 - 5 * b ^ 2 : ℤ) : Zphi) := by
        rw [hcomb, hmc]
    _ = ((s * 2 + t * (a ^ 2 - 5 * b ^ 2) : ℤ) : Zphi) := by push_cast; ring
    _ = 1 := hst'

private theorem isCoprime_conj_half (z : Zphi) (_him : Odd z.im)
    (hab : IsCoprime (sA z) (sB z)) (h5 : ¬(5 : ℤ) ∣ sA z) :
    IsCoprime z (conj z) := by
  have h5' : Prime (5 : ℤ) := by norm_num
  have ha5 : IsCoprime (sA z) (5 : ℤ) := ((Prime.coprime_iff_not_dvd h5').mpr h5).symm
  have hab5 : IsCoprime (sA z) (5 * sB z) := ha5.mul_right hab
  obtain ⟨u, v, huv⟩ := hab5
  have h1 : z + conj z = ((sA z : ℤ) : Zphi) := by
    (ext <;> simp [sA]); ring
  have h2 : z - conj z = ((sB z : ℤ) : Zphi) * sqrt5 := by
    (ext <;> simp [sB, sqrt5]); ring
  refine ⟨(u : Zphi) + (v : Zphi) * sqrt5, (u : Zphi) - (v : Zphi) * sqrt5, ?_⟩
  have key : ((u : Zphi) + (v : Zphi) * sqrt5) * z + ((u : Zphi) - (v : Zphi) * sqrt5) * conj z
      = (u : Zphi) * ((sA z : ℤ) : Zphi) + (v : Zphi) * (((sB z : ℤ) : Zphi) * sqrt5) * sqrt5 := by
    rw [← h1, ← h2]; ring
  have huv' : ((u * sA z + v * (5 * sB z) : ℤ) : Zphi) = 1 := by
    rw [huv]; norm_num
  rw [key]
  calc (u : Zphi) * ((sA z : ℤ) : Zphi) + (v : Zphi) * (((sB z : ℤ) : Zphi) * sqrt5) * sqrt5
      = (u : Zphi) * ((sA z : ℤ) : Zphi) + (v : Zphi) * ((sB z : ℤ) : Zphi) * (sqrt5 * sqrt5) := by
        ring
    _ = (u : Zphi) * ((sA z : ℤ) : Zphi) + (v : Zphi) * ((sB z : ℤ) : Zphi) * 5 := by rw [sqrt5_sq]
    _ = ((u * sA z + v * (5 * sB z) : ℤ) : Zphi) := by push_cast; ring
    _ = 1 := huv'

private theorem eq_unit_mul_pow_five (z : Zphi) (w : ℤ)
    (hcop : IsCoprime z (conj z)) (hw : norm z = w ^ 5) :
    ∃ (ε β : Zphi), IsUnit ε ∧ z = ε * β ^ 5 := by
  have h : z * conj z = ((w : Zphi)) ^ 5 := by
    rw [mul_conj, hw]; push_cast; ring
  have hg : IsUnit (gcd z (conj z)) :=
    hcop.isUnit_of_dvd' (gcd_dvd_left _ _) (gcd_dvd_right _ _)
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow hg h
  obtain ⟨u, hu⟩ := hd
  exact ⟨u, d, u.isUnit, by rw [← hu]; ring⟩

private theorem unit_congruent_of_pow (z ε β : Zphi) (a : ℤ) (hz : z = ε * β ^ 5)
    (hcong : (5 : Zphi) ∣ (z - (a : Zphi))) (hn : ¬(5 : ℤ) ∣ norm z) :
    ∃ m : ℤ, (5 : Zphi) ∣ (ε - (m : Zphi)) := by
  obtain ⟨n, hn5pow⟩ := pow_five_congr_int β
  have normpow : ∀ (x : Zphi) (k : ℕ), norm (x ^ k) = (norm x) ^ k := by
    intro x k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, norm_mul, ih, pow_succ]
  have hnint : ¬ (5 : ℤ) ∣ n := by
    intro hd
    have hcast : (5 : Zphi) ∣ (n : Zphi) := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨(k : Zphi), by exact_mod_cast congrArg (Int.cast : ℤ → Zphi) hk⟩
    have h5b : (5 : Zphi) ∣ β ^ 5 := by
      have := dvd_add hn5pow hcast
      simpa using this
    obtain ⟨v, hv⟩ := h5b
    have hnorm : (norm β) ^ 5 = 25 * norm v := by
      have := congrArg norm hv
      rw [norm_mul, normpow] at this
      simpa [norm] using this
    have h5nb : (5 : ℤ) ∣ norm β := by
      have h55 : (5 : ℤ) ∣ (norm β) ^ 5 := ⟨5 * norm v, by rw [hnorm]; ring⟩
      exact (Int.Prime.dvd_pow' (by norm_num) h55)
    apply hn
    rw [hz, norm_mul, normpow]
    obtain ⟨t, ht⟩ := h5nb
    exact ⟨norm ε * (5^4 * t^5), by rw [ht]; ring⟩
  have hfermat : (5 : ℤ) ∣ n ^ 4 - 1 := by
    have h0 : (n : ZMod 5) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast hnint
    have hx : ∀ x : ZMod 5, x ≠ 0 → x ^ 4 = 1 := by decide
    have h1 := hx _ h0
    have h2 : ((n ^ 4 - 1 : ℤ) : ZMod 5) = 0 := by push_cast [h1]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp h2
  have hfermatZ : (5 : Zphi) ∣ ((n : Zphi) ^ 4 - 1) := by
    obtain ⟨k, hk⟩ := hfermat
    exact ⟨(k : Zphi), by exact_mod_cast congrArg (Int.cast : ℤ → Zphi) hk⟩
  refine ⟨a * n ^ 3, ?_⟩
  have h1 : (5 : Zphi) ∣ ε * β ^ 5 - (a : Zphi) := by rw [← hz]; exact hcong
  have h2 : (5 : Zphi) ∣ ε * (β ^ 5 - (n : Zphi)) := hn5pow.mul_left ε
  have h3 : (5 : Zphi) ∣ ε * (n : Zphi) - (a : Zphi) := by
    have hd := dvd_sub h1 h2
    have he : ε * β ^ 5 - (a : Zphi) - ε * (β ^ 5 - (n : Zphi)) = ε * (n : Zphi) - (a : Zphi) := by
      ring
    rwa [he] at hd
  have h4 : (5 : Zphi) ∣ (ε * (n : Zphi) - (a : Zphi)) * (n : Zphi) ^ 3 := h3.mul_right _
  have h5 : (5 : Zphi) ∣ ε * ((n : Zphi) ^ 4 - 1) := hfermatZ.mul_left ε
  have h6 := dvd_sub h5 h4
  have he2 : ε - ((a * n ^ 3 : ℤ) : Zphi) =
      -(ε * ((n : Zphi) ^ 4 - 1) - (ε * (n : Zphi) - (a : Zphi)) * (n : Zphi) ^ 3) := by
    push_cast; ring
  rw [he2]
  exact dvd_neg.mpr h6

private theorem eq_pow_five_of_conj_mul (z : Zphi) (w a : ℤ)
    (hcop : IsCoprime z (conj z)) (hw : norm z = w ^ 5) (h5w : ¬(5 : ℤ) ∣ w)
    (hcong : (5 : Zphi) ∣ (z - (a : Zphi))) :
    ∃ β : Zphi, z = β ^ 5 := by
  obtain ⟨ε, β, hε, hz⟩ := eq_unit_mul_pow_five z w hcop hw
  have hn : ¬(5 : ℤ) ∣ norm z := by
    rw [hw]
    intro hd
    exact h5w (Int.Prime.dvd_pow' (by norm_num) hd)
  obtain ⟨m, hm⟩ := unit_congruent_of_pow z ε β a hz hcong hn
  obtain ⟨v, hv, hev⟩ := eq_pow_five_of_isUnit_of_congruent ε hε m hm
  exact ⟨v * β, by rw [hz, hev]; ring⟩

end Zphi

open Zphi in
private theorem key_lemma_int {a b w : ℤ} (hab : IsCoprime a b) (ha : Odd a)
    (hb : Even b) (h5a : ¬(5 : ℤ) ∣ a) (h25b : (25 : ℤ) ∣ b) (hbpos : 0 < b)
    (hw : a ^ 2 - 5 * b ^ 2 = w ^ 5) :
    ∃ c d : ℤ,
      a = c * (c ^ 4 + 50 * c ^ 2 * d ^ 2 + 125 * d ^ 4) ∧
      b = 5 * d * (c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4) ∧
      IsCoprime c d ∧ Odd c ∧ Even d ∧ ¬(5 : ℤ) ∣ c ∧ (5 : ℤ) ∣ d ∧
      c ≠ 0 ∧ 0 < d := by
  have h5' : Prime (5 : ℤ) := by norm_num
  have h5b : (5 : ℤ) ∣ b := dvd_trans (by norm_num) h25b
  set ξ := ofPair a b with hξ
  have hnorm : norm ξ = w ^ 5 := by rw [hξ, norm_ofPair, hw]
  have h5w : ¬(5 : ℤ) ∣ w := by
    intro h
    apply h5a
    apply h5'.dvd_of_dvd_pow (n := 2)
    have : a ^ 2 = w ^ 5 + 5 * b ^ 2 := by linarith
    rw [this]
    exact dvd_add (dvd_pow h (by norm_num)) ⟨b ^ 2, rfl⟩
  have hcong : (5 : Zphi) ∣ (ξ - ((a : ℤ) : Zphi)) := by
    rw [five_dvd_iff]
    constructor
    · have : (ξ - ((a : ℤ) : Zphi)).re = -b := by simp [hξ, ofPair]
      rw [this]; exact dvd_neg.mpr h5b
    · have : (ξ - ((a : ℤ) : Zphi)).im = 2 * b := by simp [hξ, ofPair]
      rw [this]; exact h5b.mul_left 2
  have hcop : IsCoprime ξ (conj ξ) := isCoprime_conj_int hab ha hb h5a
  obtain ⟨β, hβ⟩ := eq_pow_five_of_conj_mul ξ w a hcop hnorm h5w hcong
  have hsAξ : sA ξ = 2 * a := by simp [sA, hξ, ofPair]; ring
  have hsBξ : sB ξ = 2 * b := by simp [sB, hξ, ofPair]
  have hA16 : sA β * ((sA β) ^ 4 + 50 * (sA β) ^ 2 * (sB β) ^ 2 + 125 * (sB β) ^ 4)
      = 32 * a := by
    have := sA_pow_five β
    rw [← hβ, hsAξ] at this
    linarith
  have hB16 : 5 * sB β * ((sA β) ^ 4 + 10 * (sA β) ^ 2 * (sB β) ^ 2 + 5 * (sB β) ^ 4)
      = 32 * b := by
    have := sB_pow_five β
    rw [← hβ, hsBξ] at this
    linarith
  have hBeven : Even (sB β) := by
    by_contra hBodd'
    have hBodd : Odd (sB β) := Int.not_even_iff_odd.mp hBodd'
    have hAodd : Odd (sA β) := by
      have h2 : sA β % 2 = sB β % 2 := sA_parity β
      obtain ⟨m, hm⟩ := hBodd
      exact ⟨(sA β - 1) / 2, by omega⟩
    have hq := quartic_mod_32 hAodd hBodd
    obtain ⟨m, hm⟩ := hBodd
    have hdm := Int.mul_ediv_add_emod
      ((sA β) ^ 4 + 10 * (sA β) ^ 2 * (sB β) ^ 2 + 5 * (sB β) ^ 4) 32
    set Q := (sA β) ^ 4 + 10 * (sA β) ^ 2 * (sB β) ^ 2 + 5 * (sB β) ^ 4 with hQ
    set u := Q / 32 with hu
    have hQeq : Q = 32 * u + 16 := by omega
    rw [hQeq] at hB16
    have hexp : 160 * ((sB β) * u) + 80 * (sB β) = 32 * b := by
      rw [← hB16]; ring
    omega
  obtain ⟨c, d, hβcd⟩ := (eq_ofPair_iff_even_im β).mpr hBeven
  have hsAβ : sA β = 2 * c := by rw [hβcd]; simp [sA, ofPair]; ring
  have hsBβ : sB β = 2 * d := by rw [hβcd]; simp [sB, ofPair]
  rw [hsAβ, hsBβ] at hA16 hB16
  have ha_eq : a = c * (c ^ 4 + 50 * c ^ 2 * d ^ 2 + 125 * d ^ 4) := by
    have h32 : (32 : ℤ) * (c * (c ^ 4 + 50 * c ^ 2 * d ^ 2 + 125 * d ^ 4)) = 32 * a := by
      rw [← hA16]; ring
    have := mul_left_cancel₀ (by norm_num : (32 : ℤ) ≠ 0) h32
    linarith
  have hb_eq : b = 5 * d * (c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4) := by
    have h32 : (32 : ℤ) * (5 * d * (c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4)) = 32 * b := by
      rw [← hB16]; ring
    have := mul_left_cancel₀ (by norm_num : (32 : ℤ) ≠ 0) h32
    linarith
  have hc_dvd_a : c ∣ a := Dvd.intro _ ha_eq.symm
  have hd_dvd_b : d ∣ b := ⟨5 * (c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4), by rw [hb_eq]; ring⟩
  have hcd_cop : IsCoprime c d :=
    (hab.of_isCoprime_of_dvd_left hc_dvd_a).of_isCoprime_of_dvd_right hd_dvd_b
  have hc_odd : Odd c := by
    rw [ha_eq] at ha
    exact (Int.odd_mul.mp ha).1
  have hQ1_odd : Odd (c ^ 4 + 50 * c ^ 2 * d ^ 2 + 125 * d ^ 4) := by
    rw [ha_eq] at ha
    exact (Int.odd_mul.mp ha).2
  have hd_even : Even d := by
    rcases Int.even_or_odd d with h | hd_odd
    · exact h
    · exfalso
      have h1 : Odd (c ^ 4) := hc_odd.pow
      have h2 : Odd (125 * d ^ 4) := (by norm_num : Odd (125 : ℤ)).mul hd_odd.pow
      have h3 : Even (c ^ 4 + 125 * d ^ 4) := h1.add_odd h2
      have h4 : Even (50 * c ^ 2 * d ^ 2) := ⟨25 * c ^ 2 * d ^ 2, by ring⟩
      have h5 : Even (c ^ 4 + 50 * c ^ 2 * d ^ 2 + 125 * d ^ 4) := by
        have := h3.add h4
        have e : c ^ 4 + 125 * d ^ 4 + 50 * c ^ 2 * d ^ 2
            = c ^ 4 + 50 * c ^ 2 * d ^ 2 + 125 * d ^ 4 := by ring
        rwa [e] at this
      exact (Int.not_even_iff_odd.mpr hQ1_odd) h5
  have h5c : ¬(5 : ℤ) ∣ c := fun h => h5a (h.trans hc_dvd_a)
  have h5d : (5 : ℤ) ∣ d := by
    obtain ⟨b', hb'⟩ := h25b
    have h5dQ : (5 : ℤ) ∣ d * (c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4) := by
      have h5eq : 5 * (d * (c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4)) = 5 * (5 * b') := by
        linear_combination hb' - hb_eq
      have := mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h5eq
      exact ⟨b', this⟩
    rcases h5'.dvd_mul.mp h5dQ with h | h
    · exact h
    · exfalso
      apply h5c
      apply h5'.dvd_of_dvd_pow (n := 4)
      have : c ^ 4 = (c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4)
          - 5 * (2 * c ^ 2 * d ^ 2 + d ^ 4) := by ring
      rw [this]
      exact dvd_sub h ⟨2 * c ^ 2 * d ^ 2 + d ^ 4, rfl⟩
  have hc_ne : c ≠ 0 := by
    rintro rfl
    rw [ha_eq] at ha
    simp at ha
  have hd_pos : 0 < d := by
    have hQ2 := quartic_pos d hc_ne
    nlinarith [hb_eq, hbpos]
  exact ⟨c, d, ha_eq, hb_eq, hcd_cop, hc_odd, hd_even, h5c, h5d, hc_ne, hd_pos⟩

open Zphi in
private theorem key_lemma_half {a b w : ℤ} (hab : IsCoprime a b) (ha : Odd a)
    (hb : Odd b) (h5a : ¬(5 : ℤ) ∣ a) (h25b : (25 : ℤ) ∣ b) (hbpos : 0 < b)
    (hw : a ^ 2 - 5 * b ^ 2 = 4 * w ^ 5) :
    ∃ c d : ℤ,
      16 * a = c * (c ^ 4 + 50 * c ^ 2 * d ^ 2 + 125 * d ^ 4) ∧
      16 * b = 5 * d * (c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4) ∧
      IsCoprime c d ∧ Odd c ∧ Odd d ∧ ¬(5 : ℤ) ∣ c ∧ (5 : ℤ) ∣ d ∧
      c ≠ 0 ∧ 0 < d := by
  have prime5 : Prime (5 : ℤ) := by norm_num
  obtain ⟨α, hα⟩ := ha
  obtain ⟨γ, hγ⟩ := hb
  have hbodd : Odd b := ⟨γ, hγ⟩
  set ξ : Zphi := ⟨α - γ, b⟩ with hξ
  have hsA : sA ξ = a := by simp [sA, hξ]; omega
  have hsB : sB ξ = b := rfl
  have hnorm : norm ξ = w ^ 5 := by
    have h4 : 4 * norm ξ = 4 * w ^ 5 := by
      rw [four_mul_norm, hsA, hsB, hw]
    exact mul_left_cancel₀ (by norm_num) h4
  have h5w : ¬(5 : ℤ) ∣ w := by
    intro hdw
    obtain ⟨t, rfl⟩ := hdw
    have h5a2 : (5 : ℤ) ∣ a ^ 2 := ⟨b ^ 2 + 2500 * t ^ 5, by linear_combination hw⟩
    exact h5a (Int.Prime.dvd_pow' (by norm_num) h5a2)
  have him : Odd ξ.im := ⟨γ, hγ⟩
  have hcopz : IsCoprime ξ (conj ξ) := by
    apply isCoprime_conj_half ξ him
    · rw [hsA, hsB]; exact hab
    · rw [hsA]; exact h5a
  have h5b : (5 : ℤ) ∣ b := dvd_trans ⟨5, by norm_num⟩ h25b
  have hcong : (5 : Zphi) ∣ (ξ - ((α - γ : ℤ) : Zphi)) := by
    refine (five_dvd_iff _).mpr ⟨?_, ?_⟩
    · simp [hξ]
    · simpa [hξ] using h5b
  obtain ⟨β, hβ⟩ := eq_pow_five_of_conj_mul ξ w (α - γ) hcopz hnorm h5w hcong
  have h16a : 16 * a =
      sA β * ((sA β) ^ 4 + 50 * (sA β) ^ 2 * (sB β) ^ 2 + 125 * (sB β) ^ 4) := by
    have h := sA_pow_five β
    rw [← hβ, hsA] at h
    exact h
  have h16b : 16 * b =
      5 * sB β * ((sA β) ^ 4 + 10 * (sA β) ^ 2 * (sB β) ^ 2 + 5 * (sB β) ^ 4) := by
    have h := sB_pow_five β
    rw [← hβ, hsB] at h
    exact h
  have hpar : sA β % 2 = sB β % 2 := sA_parity β
  have hdodd : Odd (sB β) := by
    rcases Int.even_or_odd (sB β) with he | ho
    · exfalso
      obtain ⟨d', hd'⟩ := he
      have hce : Even (sA β) := by
        rcases Int.even_or_odd (sA β) with h | h
        · exact h
        · exfalso; obtain ⟨k, hk⟩ := h; omega
      obtain ⟨c', hc'⟩ := hce
      have h32 : 16 * b = 32 * (5 * d' * (c' ^ 4 + 10 * c' ^ 2 * d' ^ 2 + 5 * d' ^ 4)) := by
        rw [h16b, hc', hd']; ring
      omega
    · exact ho
  have hcodd : Odd (sA β) := by
    obtain ⟨dd, hdd⟩ := hdodd
    rcases Int.even_or_odd (sA β) with he | ho
    · exfalso; obtain ⟨k, hk⟩ := he; omega
    · exact ho
  have h5c : ¬(5 : ℤ) ∣ sA β := by
    intro h
    apply h5a
    have h516a : (5 : ℤ) ∣ 16 * a := by rw [h16a]; exact h.mul_right _
    rcases prime5.dvd_mul.mp h516a with h16 | ha5
    · norm_num at h16
    · exact ha5
  have h5d : (5 : ℤ) ∣ sB β := by
    obtain ⟨b', hb'⟩ := h25b
    have h16b' := h16b
    rw [hb'] at h16b'
    have hdq : sB β * ((sA β) ^ 4 + 10 * (sA β) ^ 2 * (sB β) ^ 2 + 5 * (sB β) ^ 4)
        = 80 * b' := by
      have h5eq : (5 : ℤ) * (sB β * ((sA β) ^ 4 + 10 * (sA β) ^ 2 * (sB β) ^ 2 + 5 * (sB β) ^ 4))
          = 5 * (80 * b') := by linear_combination -h16b'
      exact mul_left_cancel₀ (by norm_num) h5eq
    have h5dq : (5 : ℤ) ∣ sB β * ((sA β) ^ 4 + 10 * (sA β) ^ 2 * (sB β) ^ 2 + 5 * (sB β) ^ 4) :=
      ⟨16 * b', by rw [hdq]; ring⟩
    rcases prime5.dvd_mul.mp h5dq with h | h
    · exact h
    · exfalso
      obtain ⟨q, hq⟩ := h
      have h5c4 : (5 : ℤ) ∣ (sA β) ^ 4 :=
        ⟨q - 2 * (sA β) ^ 2 * (sB β) ^ 2 - (sB β) ^ 4, by linear_combination hq⟩
      exact h5c (Int.Prime.dvd_pow' (by norm_num) h5c4)
  have hc0 : sA β ≠ 0 := by
    intro h
    have h16a' := h16a
    rw [h] at h16a'
    simp at h16a'
    omega
  have hQpos : 0 < (sA β) ^ 4 + 10 * (sA β) ^ 2 * (sB β) ^ 2 + 5 * (sB β) ^ 4 :=
    quartic_pos (sB β) hc0
  have hdpos : 0 < sB β := by
    by_contra hle
    push Not at hle
    nlinarith [h16b, hbpos, hQpos, mul_nonpos_of_nonpos_of_nonneg hle hQpos.le]
  have hcop_cd : IsCoprime (sA β) (sB β) := by
    obtain ⟨k, hk⟩ := hcodd
    have hc2 : IsCoprime (sA β) (2 : ℤ) := ⟨1, -k, by rw [hk]; ring⟩
    have hc16 : IsCoprime (sA β) (16 : ℤ) := by
      have h := hc2.pow_right (n := 4)
      norm_num at h
      exact h
    obtain ⟨u, v, huv⟩ := hab
    obtain ⟨x, y, hxy⟩ := hc16
    refine ⟨x + y * (u * ((sA β) ^ 4 + 50 * (sA β) ^ 2 * (sB β) ^ 2 + 125 * (sB β) ^ 4)),
            y * (v * 5 * ((sA β) ^ 4 + 10 * (sA β) ^ 2 * (sB β) ^ 2 + 5 * (sB β) ^ 4)), ?_⟩
    linear_combination hxy + (16 * y) * huv - (y * u) * h16a - (y * v) * h16b
  exact ⟨sA β, sB β, h16a, h16b, hcop_cd, hcodd, hdodd, h5c, h5d, hc0, hdpos⟩

end FermatLastTheoremFive

namespace FermatLastTheoremFive

private theorem zmod25_units_pow_five :
    ∀ x y z : ZMod 25, IsUnit x → IsUnit y → IsUnit z →
      x ^ 5 + y ^ 5 ≠ z ^ 5 := by
  decide

private theorem case_one {x y z : ℤ} (hx : ¬(5 : ℤ) ∣ x) (hy : ¬(5 : ℤ) ∣ y)
    (hz : ¬(5 : ℤ) ∣ z) : x ^ 5 + y ^ 5 ≠ z ^ 5 := by
  have hunit : ∀ a : ℤ, ¬(5 : ℤ) ∣ a → IsUnit ((a : ZMod 25)) := by
    intro a ha
    have h5 : Prime (5 : ℤ) := by norm_num
    have hc : IsCoprime (5 : ℤ) a := (h5.coprime_iff_not_dvd).mpr ha
    have hc25 : IsCoprime a (25 : ℤ) := by
      have h : (25 : ℤ) = 5 ^ 2 := by norm_num
      rw [h]
      exact hc.symm.pow_right
    have hm := hc25.map (Int.castRingHom (ZMod 25))
    simp only [eq_intCast] at hm
    have h0 : ((25 : ℤ) : ZMod 25) = 0 := by decide
    rw [h0] at hm
    exact isCoprime_zero_right.mp hm
  intro h
  apply zmod25_units_pow_five (x : ZMod 25) (y : ZMod 25) (z : ZMod 25)
    (hunit x hx) (hunit y hy) (hunit z hz)
  have hc := congrArg (fun t : ℤ => (t : ZMod 25)) h
  push_cast at hc
  exact hc

end FermatLastTheoremFive

namespace FermatLastTheoremFive

private structure Desc1 where
  c : ℤ
  d : ℤ
  e : ℕ
  hcop : IsCoprime c d
  hodd : Odd c
  heven : Even d
  h5c : ¬(5 : ℤ) ∣ c
  h5d : (5 : ℤ) ∣ d
  hc0 : c ≠ 0
  hd0 : 0 < d
  hside : IsFifthPower (2 * 5 ^ e * d)
  hquartic : IsFifthPower (c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4)

private theorem exists_half_sum_diff {x y : ℤ} (hx : Odd x) (hy : Odd y)
    (hcop : IsCoprime x y) :
    ∃ p q : ℤ, x = p + q ∧ y = p - q ∧ IsCoprime p q ∧ Odd (p + q) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨a + b + 1, a - b, by omega, by omega, ⟨u + v, u - v, ?_⟩, ?_⟩
  · subst ha hb; linear_combination huv
  · exact ⟨a, by omega⟩

private theorem shape_extraction {x y z : ℤ} (hz0 : z ≠ 0) (hx : Odd x) (hy : Odd y)
    (hcop : IsCoprime x y) (h5 : (5 : ℤ) ∣ z) (heq : x ^ 5 + y ^ 5 = z ^ 5) :
    ∃ q r : ℤ, IsCoprime q r ∧ Odd (q + r) ∧ ¬(5 : ℤ) ∣ q ∧ (5 : ℤ) ∣ r ∧
      r ≠ 0 ∧
      IsFifthPower (2 * 5 ^ 2 * r) ∧
      IsFifthPower (q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4) := by
  have p5 : Prime (5 : ℤ) := by norm_num
  obtain ⟨p, q, hxpq, hypq, hpq, hoddpq⟩ := exists_half_sum_diff hx hy hcop
  have hz5 : z ^ 5 = 2 * p * (p ^ 4 + 10 * p ^ 2 * q ^ 2 + 5 * q ^ 4) := by
    rw [← heq, hxpq, hypq]; ring
  have h5p : (5 : ℤ) ∣ p := by
    have h5z5 : (5 : ℤ) ∣ z ^ 5 := dvd_pow h5 (by norm_num)
    rw [hz5] at h5z5
    rcases p5.dvd_mul.mp h5z5 with h | h
    · rcases p5.dvd_mul.mp h with h' | h'
      · norm_num at h'
      · exact h'
    · have h'' : (5 : ℤ) ∣ 10 * p ^ 2 * q ^ 2 + 5 * q ^ 4 :=
        ⟨2 * p ^ 2 * q ^ 2 + q ^ 4, by ring⟩
      have h4 := dvd_sub h h''
      have he : p ^ 4 + 10 * p ^ 2 * q ^ 2 + 5 * q ^ 4 -
          (10 * p ^ 2 * q ^ 2 + 5 * q ^ 4) = p ^ 4 := by ring
      rw [he] at h4
      exact p5.dvd_of_dvd_pow h4
  have h5q : ¬(5 : ℤ) ∣ q := fun hq =>
    absurd (Int.isUnit_iff.mp (hpq.isUnit_of_dvd' h5p hq)) (by norm_num)
  obtain ⟨r, hr⟩ := h5p
  subst hr
  have hqr : IsCoprime q r := hpq.of_mul_left_right.symm
  obtain ⟨k, hk⟩ := hoddpq
  have hoddqr : Odd (q + r) := ⟨k - 2 * r, by omega⟩
  have hz5' : z ^ 5 =
      (2 * 5 ^ 2 * r) * (q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4) := by
    rw [hz5]; ring
  have h5T : ¬(5 : ℤ) ∣ (q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4) := by
    intro h
    have h'' : (5 : ℤ) ∣ 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4 :=
      ⟨10 * q ^ 2 * r ^ 2 + 25 * r ^ 4, by ring⟩
    have h4 := dvd_sub h h''
    have he : q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4 -
        (50 * q ^ 2 * r ^ 2 + 125 * r ^ 4) = q ^ 4 := by ring
    rw [he] at h4
    exact h5q (p5.dvd_of_dvd_pow h4)
  have h5r : (5 : ℤ) ∣ r := by
    obtain ⟨u, hu⟩ := h5
    have h1 : (25 : ℤ) * (2 * r * (q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4)) =
        25 * (5 ^ 3 * u ^ 5) := by
      linear_combination (-1 : ℤ) * hz5' + (z ^ 4 + 5 * u * z ^ 3 +
        25 * u ^ 2 * z ^ 2 + 125 * u ^ 3 * z + 625 * u ^ 4) * hu
    have h2 := mul_left_cancel₀ (by norm_num : (25 : ℤ) ≠ 0) h1
    have h5lhs : (5 : ℤ) ∣ 2 * r * (q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4) := by
      rw [h2]; exact ⟨5 ^ 2 * u ^ 5, by ring⟩
    rcases p5.dvd_mul.mp h5lhs with h | h
    · rcases p5.dvd_mul.mp h with h' | h'
      · norm_num at h'
      · exact h'
    · exact absurd h h5T
  have hr0 : r ≠ 0 := by
    intro h0
    apply hz0
    have hzz : z ^ 5 = 0 := by rw [hz5', h0]; ring
    exact (pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0)).mp hzz
  have hoddT : Odd (q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4) := by
    rcases Int.even_or_odd q with ⟨m, hm⟩ | ⟨m, hm⟩ <;>
      rcases Int.even_or_odd r with ⟨n, hn⟩ | ⟨n, hn⟩
    · omega
    · exact ⟨8 * m ^ 4 + 400 * m ^ 2 * n ^ 2 + 400 * m ^ 2 * n + 100 * m ^ 2 +
        1000 * n ^ 4 + 2000 * n ^ 3 + 1500 * n ^ 2 + 500 * n + 62,
        by subst hm hn; ring⟩
    · exact ⟨8 * m ^ 4 + 16 * m ^ 3 + 12 * m ^ 2 + 4 * m + 400 * m ^ 2 * n ^ 2 +
        400 * m * n ^ 2 + 100 * n ^ 2 + 1000 * n ^ 4, by subst hm hn; ring⟩
    · omega
  have hAT : IsCoprime (2 * 5 ^ 2 * r)
      (q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4) := by
    have h2T : IsCoprime (2 : ℤ) (q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4) := by
      obtain ⟨t, ht⟩ := hoddT
      exact ⟨-t, 1, by rw [ht]; ring⟩
    have h5T' : IsCoprime (5 : ℤ) (q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4) := by
      have hq5 : IsCoprime (5 : ℤ) (q ^ 4) :=
        (p5.coprime_iff_not_dvd).mpr fun h => h5q (p5.dvd_of_dvd_pow h)
      have h := hq5.add_mul_left_right (10 * q ^ 2 * r ^ 2 + 25 * r ^ 4)
      have he : q ^ 4 + 5 * (10 * q ^ 2 * r ^ 2 + 25 * r ^ 4) =
          q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4 := by ring
      rwa [he] at h
    have hrT : IsCoprime r (q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4) := by
      have h := (hqr.symm.pow_right (n := 4)).add_mul_left_right
        (50 * q ^ 2 * r + 125 * r ^ 3)
      have he : q ^ 4 + r * (50 * q ^ 2 * r + 125 * r ^ 3) =
          q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4 := by ring
      rwa [he] at h
    exact (h2T.mul_left (h5T'.pow_left (m := 2))).mul_left hrT
  obtain ⟨hP1, hP2⟩ := int_pow_pow_of_coprime_of_mul_eq_pow hAT hz5'.symm
  exact ⟨q, r, hqr, hoddqr, h5q, h5r, hr0, hP1, hP2⟩

private theorem first_instance {q r : ℤ} (hcop : IsCoprime q r) (hpar : Odd (q + r))
    (h5q : ¬(5 : ℤ) ∣ q) (h5r : (5 : ℤ) ∣ r) (hr0 : r ≠ 0)
    (hside : IsFifthPower (2 * 5 ^ 2 * r))
    (hquart : IsFifthPower (q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4)) :
    Nonempty Desc1 := by
  have p5 : Prime (5 : ℤ) := by norm_num
  have haodd : Odd (q ^ 2 + 25 * r ^ 2) := by
    obtain ⟨k, hk⟩ := hpar
    rcases Int.even_or_odd q with ⟨m, hm⟩ | ⟨m, hm⟩ <;>
      rcases Int.even_or_odd r with ⟨n, hn⟩ | ⟨n, hn⟩
    · omega
    · exact ⟨2 * m ^ 2 + 50 * n ^ 2 + 50 * n + 12, by subst hm hn; ring⟩
    · exact ⟨2 * m ^ 2 + 2 * m + 50 * n ^ 2, by subst hm hn; ring⟩
    · omega
  have hab : IsCoprime (q ^ 2 + 25 * r ^ 2) (10 * r ^ 2) := by
    have h2 : IsCoprime (q ^ 2 + 25 * r ^ 2) 2 := by
      obtain ⟨t, ht⟩ := haodd
      exact ⟨1, -t, by rw [ht]; ring⟩
    have h5' : IsCoprime (q ^ 2 + 25 * r ^ 2) (5 : ℤ) := by
      have hq5 : IsCoprime (5 : ℤ) (q ^ 2) :=
        (p5.coprime_iff_not_dvd).mpr fun h => h5q (p5.dvd_of_dvd_pow h)
      have h := hq5.add_mul_left_right (5 * r ^ 2)
      have he : q ^ 2 + 5 * (5 * r ^ 2) = q ^ 2 + 25 * r ^ 2 := by ring
      rw [he] at h
      exact h.symm
    have hr2 : IsCoprime (q ^ 2 + 25 * r ^ 2) (r ^ 2) :=
      (hcop.pow).add_mul_right_left 25
    have h := (h2.mul_right h5').mul_right hr2
    have he : ((2 : ℤ) * 5) * r ^ 2 = 10 * r ^ 2 := by norm_num
    rwa [he] at h
  have h5a : ¬(5 : ℤ) ∣ (q ^ 2 + 25 * r ^ 2) := by
    intro h
    have h25 : (5 : ℤ) ∣ 25 * r ^ 2 := ⟨5 * r ^ 2, by ring⟩
    have h1 : (5 : ℤ) ∣ q ^ 2 := by
      have := dvd_sub h h25
      simpa using this
    exact h5q (p5.dvd_of_dvd_pow h1)
  have h25b : (25 : ℤ) ∣ 10 * r ^ 2 := by
    obtain ⟨s, hs⟩ := h5r
    exact ⟨10 * s ^ 2, by rw [hs]; ring⟩
  have hbpos : 0 < 10 * r ^ 2 := by positivity
  obtain ⟨w, hw⟩ := hquart
  have hw' : (q ^ 2 + 25 * r ^ 2) ^ 2 - 5 * (10 * r ^ 2) ^ 2 = w ^ 5 := by
    rw [← quartic_eq_sq_sub_five_sq]; exact hw
  obtain ⟨c, d, -, hbd, hcd, hodd, heven, h5c, h5d, hc0, hd0⟩ :=
    key_lemma_int hab haodd ⟨5 * r ^ 2, by ring⟩ h5a h25b hbpos hw'
  obtain ⟨s, hs⟩ := hside
  have key : (2 * 5 ^ 4 * d) * (c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4) =
      (s ^ 2) ^ 5 := by
    linear_combination (50 * r + s ^ 5) * hs + (-250 : ℤ) * hbd
  have hQodd : Odd (c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4) := by
    obtain ⟨m, hm⟩ := hodd
    obtain ⟨n, hn⟩ := heven
    exact ⟨8 * m ^ 4 + 16 * m ^ 3 + 12 * m ^ 2 + 4 * m + 80 * m ^ 2 * n ^ 2 +
      80 * m * n ^ 2 + 20 * n ^ 2 + 40 * n ^ 4, by subst hm hn; ring⟩
  have hUV : IsCoprime (2 * 5 ^ 4 * d) (c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4) := by
    have h2Q : IsCoprime (2 : ℤ) (c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4) := by
      obtain ⟨t, ht⟩ := hQodd
      exact ⟨-t, 1, by rw [ht]; ring⟩
    have h5Q : IsCoprime (5 : ℤ) (c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4) := by
      have hc5 : IsCoprime (5 : ℤ) (c ^ 4) :=
        (p5.coprime_iff_not_dvd).mpr fun h => h5c (p5.dvd_of_dvd_pow h)
      have h := hc5.add_mul_left_right (2 * c ^ 2 * d ^ 2 + d ^ 4)
      have he : c ^ 4 + 5 * (2 * c ^ 2 * d ^ 2 + d ^ 4) =
          c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4 := by ring
      rwa [he] at h
    have hdQ : IsCoprime d (c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4) := by
      have h := (hcd.symm.pow_right (n := 4)).add_mul_left_right
        (10 * c ^ 2 * d + 5 * d ^ 3)
      have he : c ^ 4 + d * (10 * c ^ 2 * d + 5 * d ^ 3) =
          c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4 := by ring
      rwa [he] at h
    exact (h2Q.mul_left (h5Q.pow_left (m := 4))).mul_left hdQ
  obtain ⟨hP1, hP2⟩ := int_pow_pow_of_coprime_of_mul_eq_pow hUV key
  exact ⟨⟨c, d, 4, hcd, hodd, heven, h5c, h5d, hc0, hd0, hP1, hP2⟩⟩

private theorem isCoprime_UV {c d : ℤ} (hcop : IsCoprime c d) (hodd : Odd c)
    (heven : Even d) (h5c : ¬(5 : ℤ) ∣ c) :
    IsCoprime (c ^ 2 + 5 * d ^ 2) (2 * d ^ 2) := by
  have hU2 : IsCoprime (c ^ 2 + 5 * d ^ 2) 2 := by
    obtain ⟨k, hk⟩ := hodd
    obtain ⟨m, hm⟩ := heven
    exact ⟨1, -(2 * k ^ 2 + 2 * k + 10 * m ^ 2), by subst hk hm; ring⟩
  have hUd : IsCoprime (c ^ 2 + 5 * d ^ 2) (d ^ 2) :=
    (hcop.pow (m := 2) (n := 2)).add_mul_right_left 5
  exact hU2.mul_right hUd

private theorem desc1_step (D : Desc1) : ∃ D' : Desc1, D'.d < D.d := by
  obtain ⟨c, d, e, hcop, hodd, heven, h5c, h5d, hc0, hd0, hside, hquartic⟩ := D
  have p5 : Prime (5 : ℤ) := by norm_num
  have hab : IsCoprime (c ^ 2 + 5 * d ^ 2) (2 * d ^ 2) :=
    isCoprime_UV hcop hodd heven h5c
  have haodd : Odd (c ^ 2 + 5 * d ^ 2) := by
    obtain ⟨m, hm⟩ := hodd
    obtain ⟨n, hn⟩ := heven
    exact ⟨2 * m ^ 2 + 2 * m + 10 * n ^ 2, by subst hm hn; ring⟩
  have h5U : ¬(5 : ℤ) ∣ (c ^ 2 + 5 * d ^ 2) := by
    intro h
    have h1 : (5 : ℤ) ∣ c ^ 2 := by
      have h5d2 : (5 : ℤ) ∣ 5 * d ^ 2 := ⟨d ^ 2, rfl⟩
      have := dvd_sub h h5d2
      simpa using this
    exact h5c (p5.dvd_of_dvd_pow h1)
  have h25V : (25 : ℤ) ∣ 2 * d ^ 2 := by
    obtain ⟨t, ht⟩ := h5d
    exact ⟨2 * t ^ 2, by rw [ht]; ring⟩
  have hVpos : 0 < 2 * d ^ 2 := by nlinarith [hd0]
  obtain ⟨w, hw⟩ := hquartic
  have hw' : (c ^ 2 + 5 * d ^ 2) ^ 2 - 5 * (2 * d ^ 2) ^ 2 = w ^ 5 := by
    rw [← quartic_eq_sq_sub_five_sq']; exact hw
  obtain ⟨c', d', -, hbd, hcd', hodd', heven', h5c', h5d', hc0', hd0'⟩ :=
    key_lemma_int hab haodd ⟨d ^ 2, by ring⟩ h5U h25V hVpos hw'
  obtain ⟨s, hs⟩ := hside
  have key : (2 * 5 ^ (2 * e + 1) * d') *
      (c' ^ 4 + 10 * c' ^ 2 * d' ^ 2 + 5 * d' ^ 4) = (s ^ 2) ^ 5 := by
    linear_combination (2 * 5 ^ e * d + s ^ 5) * hs +
      (-(2 * 5 ^ (2 * e) : ℤ)) * hbd
  have hQodd : Odd (c' ^ 4 + 10 * c' ^ 2 * d' ^ 2 + 5 * d' ^ 4) := by
    obtain ⟨m, hm⟩ := hodd'
    obtain ⟨n, hn⟩ := heven'
    exact ⟨8 * m ^ 4 + 16 * m ^ 3 + 12 * m ^ 2 + 4 * m + 80 * m ^ 2 * n ^ 2 +
      80 * m * n ^ 2 + 20 * n ^ 2 + 40 * n ^ 4, by subst hm hn; ring⟩
  have hUV : IsCoprime (2 * 5 ^ (2 * e + 1) * d')
      (c' ^ 4 + 10 * c' ^ 2 * d' ^ 2 + 5 * d' ^ 4) := by
    have h2Q : IsCoprime (2 : ℤ) (c' ^ 4 + 10 * c' ^ 2 * d' ^ 2 + 5 * d' ^ 4) := by
      obtain ⟨t, ht⟩ := hQodd
      exact ⟨-t, 1, by rw [ht]; ring⟩
    have h5Q : IsCoprime (5 : ℤ) (c' ^ 4 + 10 * c' ^ 2 * d' ^ 2 + 5 * d' ^ 4) := by
      have hc5 : IsCoprime (5 : ℤ) (c' ^ 4) :=
        (p5.coprime_iff_not_dvd).mpr fun h => h5c' (p5.dvd_of_dvd_pow h)
      have h := hc5.add_mul_left_right (2 * c' ^ 2 * d' ^ 2 + d' ^ 4)
      have he : c' ^ 4 + 5 * (2 * c' ^ 2 * d' ^ 2 + d' ^ 4) =
          c' ^ 4 + 10 * c' ^ 2 * d' ^ 2 + 5 * d' ^ 4 := by ring
      rwa [he] at h
    have hdQ : IsCoprime d' (c' ^ 4 + 10 * c' ^ 2 * d' ^ 2 + 5 * d' ^ 4) := by
      have h := (hcd'.symm.pow_right (n := 4)).add_mul_left_right
        (10 * c' ^ 2 * d' + 5 * d' ^ 3)
      have he : c' ^ 4 + d' * (10 * c' ^ 2 * d' + 5 * d' ^ 3) =
          c' ^ 4 + 10 * c' ^ 2 * d' ^ 2 + 5 * d' ^ 4 := by ring
      rwa [he] at h
    exact (h2Q.mul_left (h5Q.pow_left (m := 2 * e + 1))).mul_left hdQ
  obtain ⟨hP1, hP2⟩ := int_pow_pow_of_coprime_of_mul_eq_pow hUV key
  have hd'lt : d' < d := by
    have h1 : 1 ≤ c' ^ 2 := by rcases lt_or_gt_of_ne hc0' with h | h <;> nlinarith
    have hQge : 5 * d' ^ 4 + 1 ≤ c' ^ 4 + 10 * c' ^ 2 * d' ^ 2 + 5 * d' ^ 4 := by
      nlinarith [sq_nonneg (c' * d'), sq_nonneg (c' ^ 2)]
    have h2 : 25 * d' ^ 5 + 5 * d' ≤ 2 * d ^ 2 := by
      rw [hbd]
      nlinarith [hd0', hQge]
    by_contra hle
    push Not at hle
    have hd1 : (1 : ℤ) ≤ d' := by omega
    have h3 : d ^ 2 ≤ d' ^ 2 := pow_le_pow_left₀ (le_of_lt hd0) hle 2
    have h4 : d' ^ 2 ≤ d' ^ 5 := pow_le_pow_right₀ hd1 (by norm_num)
    linarith [sq_nonneg d']
  exact ⟨⟨c', d', 2 * e + 1, hcd', hodd', heven', h5c', h5d', hc0', hd0',
    hP1, hP2⟩, hd'lt⟩

private theorem desc1_false : ¬ Nonempty Desc1 := by
  rintro ⟨D⟩
  have key : ∀ n : ℕ, ∀ D : Desc1, D.d.toNat ≤ n → False := by
    intro n
    induction n with
    | zero => intro D hD; have := D.hd0; omega
    | succ n ih =>
      intro D hD
      obtain ⟨D', hlt⟩ := desc1_step D
      exact ih D' (by have := D'.hd0; omega)
  exact key D.d.toNat D le_rfl

private theorem case_two_even {x y z : ℤ} (hz0 : z ≠ 0) (hx : Odd x) (hy : Odd y)
    (hcop : IsCoprime x y) (h5 : (5 : ℤ) ∣ z) :
    x ^ 5 + y ^ 5 ≠ z ^ 5 := by
  intro heq
  obtain ⟨q, r, hc, hpar, h5q, h5r, hr0, hside, hquart⟩ :=
    shape_extraction hz0 hx hy hcop h5 heq
  exact desc1_false (first_instance hc hpar h5q h5r hr0 hside hquart)

end FermatLastTheoremFive

namespace FermatLastTheoremFive

private structure Desc2 where
  c : ℤ
  d : ℤ
  e : ℕ
  hcop : IsCoprime c d
  hcodd : Odd c
  hdodd : Odd d
  h5c : ¬(5 : ℤ) ∣ c
  h5d : (5 : ℤ) ∣ d
  hd0 : 0 < d
  hside : IsFifthPower (5 ^ e * d)
  hquartic : ∃ w : ℤ, c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4 = 16 * w ^ 5

private theorem shape_extraction_odd {x y z : ℤ} (_hx0 : x ≠ 0) (hy : Odd y)
    (hz : Even z) (hcop : IsCoprime y z) (h5x : (5 : ℤ) ∣ x)
    (heq : x ^ 5 + y ^ 5 = z ^ 5) :
    ∃ q r : ℤ, IsCoprime q r ∧ Odd q ∧ Odd r ∧ ¬(5 : ℤ) ∣ q ∧ (5 : ℤ) ∣ r ∧
      IsFifthPower (5 ^ 2 * r) ∧
      (∃ w : ℤ, q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4 = 16 * w ^ 5) := by
  have hp5 : Prime (5 : ℤ) := by norm_num
  obtain ⟨p, hp_def⟩ : ∃ p : ℤ, p = z - y := ⟨_, rfl⟩
  obtain ⟨q, hq_def⟩ : ∃ q : ℤ, q = z + y := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ := hy
  obtain ⟨n, hn⟩ := hz
  have hpodd : Odd p := ⟨n - m - 1, by omega⟩
  have hqodd : Odd q := ⟨n + m, by omega⟩
  have hkey : 32 * x ^ 5 = 2 * p * (p ^ 4 + 10 * p ^ 2 * q ^ 2 + 5 * q ^ 4) := by
    rw [hp_def, hq_def]
    linear_combination 32 * heq
  have hpq : IsCoprime p q := by
    obtain ⟨u, v, huv⟩ := hcop
    obtain ⟨k, hk⟩ := hpodd
    refine ⟨1 - k * (v - u), -(k * (v + u)), ?_⟩
    rw [hp_def] at hk
    rw [hp_def, hq_def]
    linear_combination hk - 2 * k * huv
  have h5p : (5 : ℤ) ∣ p := by
    have h1 : (5 : ℤ) ∣ 2 * p * (p ^ 4 + 10 * p ^ 2 * q ^ 2 + 5 * q ^ 4) := by
      rw [← hkey]
      exact Dvd.dvd.mul_left (dvd_pow h5x (by norm_num)) 32
    rcases hp5.dvd_mul.mp h1 with h2 | h2
    · rcases hp5.dvd_mul.mp h2 with h3 | h3
      · norm_num at h3
      · exact h3
    · have h4 : (5 : ℤ) ∣ p ^ 4 := by
        have hrw : p ^ 4 =
            (p ^ 4 + 10 * p ^ 2 * q ^ 2 + 5 * q ^ 4) -
              5 * (2 * p ^ 2 * q ^ 2 + q ^ 4) := by ring
        rw [hrw]
        exact dvd_sub h2 ⟨2 * p ^ 2 * q ^ 2 + q ^ 4, rfl⟩
      exact hp5.dvd_of_dvd_pow h4
  have h5q : ¬(5 : ℤ) ∣ q := by
    intro h
    have hu := hpq.isUnit_of_dvd' h5p h
    rw [Int.isUnit_iff] at hu
    norm_num at hu
  obtain ⟨r, hr⟩ := h5p
  have hrodd : Odd r := by
    rw [Int.odd_iff] at hpodd ⊢
    omega
  have hqr : IsCoprime q r :=
    hpq.symm.of_isCoprime_of_dvd_right ⟨5, by rw [hr]; ring⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℤ, Q = q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4 :=
    ⟨_, rfl⟩
  have hkey2 : 32 * x ^ 5 = 2 * 5 ^ 2 * r * Q := by
    rw [hQdef, hkey, hr]; ring
  have h5Q : ¬(5 : ℤ) ∣ Q := by
    intro h
    have h4 : (5 : ℤ) ∣ q ^ 4 := by
      have hrw : q ^ 4 = Q - 5 * (10 * q ^ 2 * r ^ 2 + 25 * r ^ 4) := by
        rw [hQdef]; ring
      rw [hrw]
      exact dvd_sub h ⟨10 * q ^ 2 * r ^ 2 + 25 * r ^ 4, rfl⟩
    exact h5q (hp5.dvd_of_dvd_pow h4)
  have h5r : (5 : ℤ) ∣ r := by
    obtain ⟨t, ht⟩ := pow_dvd_pow_of_dvd h5x 5
    have h3 : (5 : ℤ) ^ 2 * (2 * r * Q) = 5 ^ 2 * (5 ^ 3 * 32 * t) := by
      linear_combination -hkey2 + 32 * ht
    have h4 := mul_left_cancel₀ (by norm_num : ((5 : ℤ) ^ 2) ≠ 0) h3
    have h5 : (5 : ℤ) ∣ 2 * r * Q := ⟨5 ^ 2 * 32 * t, by rw [h4]; ring⟩
    rcases hp5.dvd_mul.mp h5 with h6 | h6
    · rcases hp5.dvd_mul.mp h6 with h7 | h7
      · norm_num at h7
      · exact h7
    · exact absurd h6 h5Q
  have hmod : (p ^ 4 + 10 * p ^ 2 * q ^ 2 + 5 * q ^ 4) % 32 = 16 :=
    quartic_mod_32 hpodd hqodd
  have h5Qeq : p ^ 4 + 10 * p ^ 2 * q ^ 2 + 5 * q ^ 4 = 5 * Q := by
    rw [hQdef, hr]; ring
  have hQmod : Q % 32 = 16 := by rw [h5Qeq] at hmod; omega
  obtain ⟨Q', hQ'⟩ : ∃ Q' : ℤ, Q = 16 * Q' := ⟨Q / 16, by omega⟩
  have h32 : (32 : ℤ) * x ^ 5 = 32 * (5 ^ 2 * r * Q') := by
    linear_combination hkey2 + 2 * 5 ^ 2 * r * hQ'
  have hx5 : 5 ^ 2 * r * Q' = x ^ 5 :=
    (mul_left_cancel₀ (by norm_num : (32 : ℤ) ≠ 0) h32).symm
  have hQ'dvd : Q' ∣ Q := ⟨16, by rw [hQ']; ring⟩
  have h5Q' : ¬(5 : ℤ) ∣ Q' := fun h => h5Q (h.trans hQ'dvd)
  have hrQ : IsCoprime r Q := by
    have h1 : IsCoprime r (q ^ 4) := hqr.symm.pow_right
    have h2 := h1.add_mul_left_right (50 * q ^ 2 * r + 125 * r ^ 3)
    have hrw : Q = q ^ 4 + r * (50 * q ^ 2 * r + 125 * r ^ 3) := by
      rw [hQdef]; ring
    rw [hrw]; exact h2
  have hrQ' : IsCoprime r Q' := hrQ.of_isCoprime_of_dvd_right hQ'dvd
  have hcop' : IsCoprime (5 ^ 2 * r) Q' :=
    ((hp5.coprime_iff_not_dvd.mpr h5Q').pow_left).mul_left hrQ'
  obtain ⟨hfifth, hQ'fifth⟩ := int_pow_pow_of_coprime_of_mul_eq_pow hcop' hx5
  obtain ⟨w, hw⟩ := hQ'fifth
  exact ⟨q, r, hqr, hqodd, hrodd, h5q, h5r, hfifth,
    ⟨w, by linear_combination -hQdef + hQ' + 16 * hw⟩⟩

private theorem first_instance_odd {q r : ℤ} (hcop : IsCoprime q r) (hq : Odd q)
    (hr : Odd r) (h5q : ¬(5 : ℤ) ∣ q) (h5r : (5 : ℤ) ∣ r)
    (hside : IsFifthPower (5 ^ 2 * r))
    (hquart : ∃ w : ℤ, q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4 = 16 * w ^ 5) :
    Nonempty Desc2 := by
  have p5 : Prime (5 : ℤ) := by norm_num
  obtain ⟨m, hm⟩ := hq
  obtain ⟨n, hn⟩ := hr
  obtain ⟨a, ha_def⟩ : ∃ a : ℤ, a = 2 * m ^ 2 + 2 * m + 50 * n ^ 2 + 50 * n + 13 :=
    ⟨_, rfl⟩
  have ha : 2 * a = q ^ 2 + 25 * r ^ 2 := by rw [ha_def, hm, hn]; ring
  have haodd : Odd a := ⟨m ^ 2 + m + 25 * n ^ 2 + 25 * n + 6, by rw [ha_def]; ring⟩
  have hbodd : Odd (5 * r ^ 2) := ⟨10 * n ^ 2 + 10 * n + 2, by rw [hn]; ring⟩
  have h5a : ¬(5 : ℤ) ∣ a := by
    intro h
    have hq2 : q ^ 2 = 2 * a - 25 * r ^ 2 := by linear_combination -ha
    have h1 : (5 : ℤ) ∣ q ^ 2 := by
      rw [hq2]
      exact dvd_sub (h.mul_left 2) ⟨5 * r ^ 2, by ring⟩
    exact h5q (p5.dvd_of_dvd_pow h1)
  have har : IsCoprime a r := by
    obtain ⟨u, v, huv⟩ := hcop
    exact ⟨2 * u ^ 2, 2 * u * v * q + v ^ 2 * r - 25 * u ^ 2 * r, by
      linear_combination u ^ 2 * ha + (u * q + v * r + 1) * huv⟩
  have hab : IsCoprime a (5 * r ^ 2) :=
    ((p5.coprime_iff_not_dvd.mpr h5a).symm).mul_right har.pow_right
  have h25b : (25 : ℤ) ∣ 5 * r ^ 2 := by
    obtain ⟨r', hr'⟩ := h5r
    exact ⟨5 * r' ^ 2, by rw [hr']; ring⟩
  have hr0 : r ≠ 0 := by rw [hn]; omega
  have hbpos : 0 < 5 * r ^ 2 := by positivity
  obtain ⟨w, hw⟩ := hquart
  have h4w : 4 * (a ^ 2 - 5 * (5 * r ^ 2) ^ 2) = 4 * (4 * w ^ 5) := by
    linear_combination (2 * a + q ^ 2 + 25 * r ^ 2) * ha + hw
  have hw4 : a ^ 2 - 5 * (5 * r ^ 2) ^ 2 = 4 * w ^ 5 :=
    mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h4w
  obtain ⟨c, d, -, h16b, hcd, hcodd, hdodd, h5c, h5d, -, hd0⟩ :=
    key_lemma_half hab haodd hbodd h5a h25b hbpos hw4
  have hmodcd : (c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4) % 32 = 16 :=
    quartic_mod_32 hcodd hdodd
  obtain ⟨k, hk⟩ : ∃ k : ℤ, c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4 = 16 * k :=
    ⟨(c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4) / 16, by omega⟩
  have h80 : (80 : ℤ) * (r ^ 2) = 80 * (d * k) := by
    linear_combination h16b + 5 * d * hk
  have hrk2 : r ^ 2 = d * k := mul_left_cancel₀ (by norm_num : (80 : ℤ) ≠ 0) h80
  obtain ⟨s, hs⟩ := hside
  have key : 5 ^ 4 * d * k = (s ^ 2) ^ 5 := by
    linear_combination (5 ^ 2 * r + s ^ 5) * hs - 625 * hrk2
  have h5X : ¬(5 : ℤ) ∣ (c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4) := by
    intro h
    have h1 : (5 : ℤ) ∣ c ^ 4 := by
      have hrw : c ^ 4 =
          (c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4) -
            5 * (2 * c ^ 2 * d ^ 2 + d ^ 4) := by ring
      rw [hrw]
      exact dvd_sub h ⟨2 * c ^ 2 * d ^ 2 + d ^ 4, rfl⟩
    exact h5c (p5.dvd_of_dvd_pow h1)
  have h5k : ¬(5 : ℤ) ∣ k := fun h => h5X (by rw [hk]; exact h.mul_left 16)
  have hdX : IsCoprime d (c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4) := by
    have h1 : IsCoprime d (c ^ 4) := hcd.symm.pow_right
    have h2 := h1.add_mul_left_right (10 * c ^ 2 * d + 5 * d ^ 3)
    have hrw : c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4 =
        c ^ 4 + d * (10 * c ^ 2 * d + 5 * d ^ 3) := by ring
    rw [hrw]; exact h2
  have hdk : IsCoprime d k :=
    hdX.of_isCoprime_of_dvd_right ⟨16, by linear_combination hk⟩
  have hcop'' : IsCoprime (5 ^ 4 * d) k :=
    ((p5.coprime_iff_not_dvd.mpr h5k).pow_left).mul_left hdk
  obtain ⟨hside', hkfifth⟩ := int_pow_pow_of_coprime_of_mul_eq_pow hcop'' key
  obtain ⟨w', hw'⟩ := hkfifth
  exact ⟨⟨c, d, 4, hcd, hcodd, hdodd, h5c, h5d, hd0, hside',
    ⟨w', by rw [hk, hw']⟩⟩⟩

private theorem isCoprime_AB {c d A : ℤ} (hcop : IsCoprime c d) (_hcodd : Odd c)
    (_hdodd : Odd d) (_h5c : ¬(5 : ℤ) ∣ c) (hA : 2 * A = c ^ 2 + 5 * d ^ 2) :
    IsCoprime A (d ^ 2) := by
  obtain ⟨u, v, huv⟩ := hcop
  have h2 : (u * c + v * d) ^ 2 = 1 := by rw [huv]; ring
  have h : IsCoprime A d :=
    ⟨2 * u ^ 2, 2 * u * c * v + v ^ 2 * d - 5 * u ^ 2 * d, by
      linear_combination h2 + u ^ 2 * hA⟩
  exact h.pow_right

private theorem desc2_step (D : Desc2) : ∃ D' : Desc2, D'.d < D.d := by
  obtain ⟨c, d, e, hcd, hcodd, hdodd, h5c, h5d, hd0, hside, hquartic⟩ := D
  have h5 : Prime (5 : ℤ) := by norm_num
  obtain ⟨j, hj⟩ := id hcodd
  obtain ⟨l, hl⟩ := id hdodd
  obtain ⟨A, hAval⟩ : ∃ A : ℤ, A = 2*j^2 + 2*j + 10*l^2 + 10*l + 3 := ⟨_, rfl⟩
  have hA : 2 * A = c ^ 2 + 5 * d ^ 2 := by rw [hAval, hj, hl]; ring
  have hAodd : Odd A := ⟨j^2 + j + 5*l^2 + 5*l + 1, by rw [hAval]; ring⟩
  have hBodd : Odd (d ^ 2) := hdodd.pow
  have hcopAB : IsCoprime A (d ^ 2) := isCoprime_AB hcd hcodd hdodd h5c hA
  have h5A : ¬(5 : ℤ) ∣ A := by
    intro h5a
    obtain ⟨t, ht⟩ := h5a
    have hc2 : (5 : ℤ) ∣ c ^ 2 := ⟨2*t - d^2, by linarith [hA]⟩
    exact h5c (h5.dvd_of_dvd_pow hc2)
  have h25B : (25 : ℤ) ∣ d ^ 2 := by
    obtain ⟨s, hs⟩ := h5d
    exact ⟨s ^ 2, by rw [hs]; ring⟩
  have hB0 : 0 < d ^ 2 := pow_pos hd0 2
  obtain ⟨w, hwq⟩ := hquartic
  have h4 : 4 * (A ^ 2 - 5 * (d ^ 2) ^ 2) = 4 * (4 * w ^ 5) := by
    linear_combination (2*A + c^2 + 5*d^2) * hA + hwq
  have hw5 : A ^ 2 - 5 * (d ^ 2) ^ 2 = 4 * w ^ 5 := by linarith
  obtain ⟨c', d', h16A, h16B, hcd', hcodd', hdodd', h5c', h5d', hc0', hd0'⟩ :=
    key_lemma_half hcopAB hAodd hBodd h5A h25B hB0 hw5
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℤ, Q = c' ^ 4 + 10 * c' ^ 2 * d' ^ 2 + 5 * d' ^ 4 :=
    ⟨_, rfl⟩
  rw [← hQdef] at h16B
  have hQ32 : Q % 32 = 16 := by rw [hQdef]; exact quartic_mod_32 hcodd' hdodd'
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Q = 32 * k + 16 := ⟨Q / 32, by omega⟩
  obtain ⟨Q₁, hQ₁val⟩ : ∃ q : ℤ, q = 2 * k + 1 := ⟨_, rfl⟩
  have hQ16 : Q = 16 * Q₁ := by rw [hQ₁val]; omega
  have hd2 : d ^ 2 = 5 * d' * Q₁ :=
    mul_left_cancel₀ (by norm_num : (16 : ℤ) ≠ 0)
      (by linear_combination h16B + 5 * d' * hQ16)
  obtain ⟨m, hm⟩ := hside
  have hprod : 5 ^ (2*e+1) * d' * Q₁ = (m ^ 2) ^ 5 := by
    have h1 : (5 ^ e * d) ^ 2 = (m ^ 2) ^ 5 := by rw [hm]; ring
    rw [← h1, mul_pow, hd2]; ring
  have hdQ : IsCoprime d' Q₁ := by
    have h1 : IsCoprime d' (c' ^ 4) := hcd'.symm.pow_right
    have h2 : IsCoprime d' (16 * Q₁) := by
      rw [← hQ16, hQdef,
        show c' ^ 4 + 10 * c' ^ 2 * d' ^ 2 + 5 * d' ^ 4
            = c' ^ 4 + d' * (10 * c' ^ 2 * d' + 5 * d' ^ 3) by ring]
      exact h1.add_mul_left_right _
    exact h2.of_mul_right_right
  have h5Q : ¬(5 : ℤ) ∣ Q₁ := by
    intro hdvd
    apply h5c'
    obtain ⟨t, ht⟩ := hdvd
    have hQeq : c' ^ 4 + 10 * c' ^ 2 * d' ^ 2 + 5 * d' ^ 4 = 16 * Q₁ := by
      rw [← hQdef]; exact hQ16
    have h5c4 : (5 : ℤ) ∣ c' ^ 4 :=
      ⟨16 * t - 2 * c' ^ 2 * d' ^ 2 - d' ^ 4, by linarith [hQeq]⟩
    exact h5.dvd_of_dvd_pow h5c4
  have hcop5 : IsCoprime ((5 : ℤ) ^ (2*e+1) * d') Q₁ :=
    ((h5.coprime_iff_not_dvd.mpr h5Q).pow_left).mul_left hdQ
  have hside' : IsFifthPower (5 ^ (2*e+1) * d') :=
    int_pow_of_coprime_of_mul_eq_pow hcop5 hprod
  obtain ⟨w', hw'⟩ : IsFifthPower Q₁ :=
    int_pow_of_coprime_of_mul_eq_pow hcop5.symm (by rw [mul_comm]; exact hprod)
  refine ⟨⟨c', d', 2*e+1, hcd', hcodd', hdodd', h5c', h5d', hd0', hside',
    ⟨w', by rw [← hQdef, hQ16, hw']⟩⟩, ?_⟩
  change d' < d
  by_contra hnot
  have hle : d ≤ d' := not_lt.mp hnot
  have hd1 : (1 : ℤ) ≤ d := by omega
  have hd'1 : (1 : ℤ) ≤ d' := by omega
  have hc'1 : (1 : ℤ) ≤ c' ^ 2 := by nlinarith [Int.one_le_abs hc0', sq_abs c']
  have hQlow : 5 * d' ^ 4 + 10 * d' ^ 2 + 1 ≤ Q := by
    have h4' : (1 : ℤ) ≤ c' ^ 4 := by nlinarith [hc'1]
    have hmid : 10 * d' ^ 2 ≤ 10 * c' ^ 2 * d' ^ 2 := by
      nlinarith [hc'1, sq_nonneg d']
    rw [hQdef]
    linarith [h4', hmid]
  have hd35 : d ^ 5 ≤ d' ^ 5 := pow_le_pow_left₀ hd0.le hle 5
  have hd'31 : (1 : ℤ) ≤ d' ^ 3 := one_le_pow₀ hd'1
  have h25 : d ^ 2 ≤ d ^ 5 := by
    have hd31 : (1 : ℤ) ≤ d ^ 3 := one_le_pow₀ hd1
    nlinarith [hd31, pow_pos hd0 2]
  have hmul : 5 * d' * (5 * d' ^ 4 + 10 * d' ^ 2 + 1) ≤ 5 * d' * Q :=
    mul_le_mul_of_nonneg_left hQlow (by linarith)
  have hbig : 25 * d' ^ 5 + 50 * d' ^ 3 + 5 * d' ≤ 16 * d ^ 2 := by
    linarith [hmul, h16B]
  linarith [hbig, hd35, h25, hd'31, hd'1, pow_pos hd0 2]

private theorem desc2_false : ¬ Nonempty Desc2 := by
  rintro ⟨D₀⟩
  have key : ∀ n : ℕ, ∀ D : Desc2, D.d.toNat = n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro D hD
      obtain ⟨D', hlt⟩ := desc2_step D
      have h1 := D'.hd0
      exact ih D'.d.toNat (by omega) D' rfl
  exact key D₀.d.toNat D₀ rfl

private theorem case_two_odd {x y z : ℤ} (hx0 : x ≠ 0) (_hxodd : Odd x) (hy : Odd y)
    (hz : Even z) (hcopyz : IsCoprime y z) (h5x : (5 : ℤ) ∣ x) :
    x ^ 5 + y ^ 5 ≠ z ^ 5 := by
  intro heq
  obtain ⟨q, r, hcop, hq, hr, h5q, h5r, hside, hquart⟩ :=
    shape_extraction_odd hx0 hy hz hcopyz h5x heq
  exact desc2_false (first_instance_odd hcop hq hr h5q h5r hside hquart)

end FermatLastTheoremFive

namespace FermatLastTheoremFive

private theorem normalize_parity {x y z : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (heq : x ^ 5 + y ^ 5 = z ^ 5) :
    ∃ a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
      Odd a ∧ Odd b ∧ Even c ∧
      IsCoprime a b ∧ IsCoprime b c ∧ IsCoprime a c ∧
      a ^ 5 + b ^ 5 = c ^ 5 ∧
      (a * b * c).natAbs = (x * y * z).natAbs := by
  rcases Int.even_or_odd x with hxe | hxo
  · have hyo : Odd y := by
      rcases Int.even_or_odd y with hye | hyo
      · exact absurd (Int.isUnit_iff.mp (hxy.isUnit_of_dvd' hxe.two_dvd hye.two_dvd))
          (by norm_num)
      · exact hyo
    have hzo : Odd z := by
      have h5 : Odd (z ^ 5) := by
        rw [← heq]
        exact (Int.even_pow.mpr ⟨hxe, by norm_num⟩).add_odd hyo.pow
      exact (Int.odd_pow.mp h5).resolve_right (by norm_num)
    refine ⟨y, -z, -x, hy, neg_ne_zero.mpr hz, neg_ne_zero.mpr hx,
      hyo, hzo.neg, hxe.neg, hyz.neg_right, ?_, hxy.symm.neg_right,
      by linear_combination heq, by rw [show y * -z * -x = x * y * z by ring]⟩
    exact hxz.symm.neg_left.neg_right
  · rcases Int.even_or_odd y with hye | hyo
    · have hzo : Odd z := by
        have h5 : Odd (z ^ 5) := by
          rw [← heq, add_comm]
          exact (Int.even_pow.mpr ⟨hye, by norm_num⟩).add_odd hxo.pow
        exact (Int.odd_pow.mp h5).resolve_right (by norm_num)
      refine ⟨x, -z, -y, hx, neg_ne_zero.mpr hz, neg_ne_zero.mpr hy,
        hxo, hzo.neg, hye.neg, hxz.neg_right, ?_, hxy.neg_right,
        by linear_combination heq, by rw [show x * -z * -y = x * y * z by ring]⟩
      exact hyz.symm.neg_left.neg_right
    · have hze : Even z := by
        have h5 : Even (z ^ 5) := by
          rw [← heq]; exact hxo.pow.add_odd hyo.pow
        exact (Int.even_pow.mp h5).1
      exact ⟨x, y, z, hx, hy, hz, hxo, hyo, hze, hxy, hyz, hxz, heq, rfl⟩

private theorem flt_five_coprime {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hao : Odd a) (hbo : Odd b) (hce : Even c)
    (hab : IsCoprime a b) (hbc : IsCoprime b c) (hac : IsCoprime a c) :
    a ^ 5 + b ^ 5 ≠ c ^ 5 := by
  by_cases h5c : (5 : ℤ) ∣ c
  · exact case_two_even hc hao hbo hab h5c
  by_cases h5a : (5 : ℤ) ∣ a
  · exact case_two_odd ha hao hbo hce hbc h5a
  by_cases h5b : (5 : ℤ) ∣ b
  · rw [add_comm]
    exact case_two_odd hb hbo hao hce hac h5b
  exact case_one h5a h5b h5c

private theorem flt_five_int : FermatLastTheoremWith ℤ 5 := by
  refine fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
    (fun x y z hx hy hz Hgcd ↦ ?_)
  intro heq
  have Hg : Finset.gcd {x, y, -z} id = 1 := by
    simp only [← Hgcd, Finset.gcd_insert, Finset.gcd_singleton, id_eq,
      ← Int.abs_eq_normalize, abs_neg]
  have Hg2 : Finset.gcd {y, -z, x} id = 1 := by
    rw [Finset.pair_comm (-z) x, Finset.insert_comm y x]; exact Hg
  have Hg3 : Finset.gcd {x, -z, y} id = 1 := by
    rw [Finset.pair_comm (-z) y]; exact Hg
  have hxy : IsCoprime x y :=
    isCoprime_of_gcd_eq_one_of_FLT Hg (n := 5) (by linear_combination heq)
  have hyz : IsCoprime y z := by
    have h := isCoprime_of_gcd_eq_one_of_FLT Hg2 (n := 5) (by linear_combination heq)
    simpa using h.neg_right
  have hxz : IsCoprime x z := by
    have h := isCoprime_of_gcd_eq_one_of_FLT Hg3 (n := 5) (by linear_combination heq)
    simpa using h.neg_right
  obtain ⟨a, b, c, ha, hb, hc, hao, hbo, hce, hab, hbc, hac, heq5, -⟩ :=
    normalize_parity hx hy hz hxy hyz hxz heq
  exact flt_five_coprime ha hb hc hao hbo hce hab hbc hac heq5

end FermatLastTheoremFive

/-- **Fermat's Last Theorem for exponent 5.** -/
public theorem fermatLastTheoremFive : FermatLastTheoremFor 5 := by
  rw [fermatLastTheoremFor_iff_int]
  exact FermatLastTheoremFive.flt_five_int

end

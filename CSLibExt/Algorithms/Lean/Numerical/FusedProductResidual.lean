/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Numerical.FloatingPoint

/-!
# Error-free product residual by fused multiply-add

In the binary value model, a fused multiply-add rounds the exact value `a * b - π` once.
We prove that this value is representable, including as a subnormal, under a lower bound
on the sum of the operand exponents and the assumption that the rounded product `π` is finite.
This is the TwoProductFMA construction of Ogita, Rump and Oishi, *Accurate Sum and Dot Product*,
Algorithm 3.5. The exponent condition here ensures representability in a bounded format.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FloatingPoint

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

omit [FloorRing K] in
private theorem abs_int_mul_zpow_lt_iff {p : ℕ} {m e : ℤ} :
    |(m : K) * 2 ^ e| < 2 ^ (e + p) ↔ |m| < 2 ^ p := by
  have he : (0 : K) < 2 ^ e := zpow_pos two_pos e
  rw [abs_mul, abs_of_pos he, zpow_add₀ two_ne_zero, zpow_natCast, mul_comm ((2 : K) ^ e),
    mul_lt_mul_iff_left₀ he]
  norm_cast

private theorem ulpExp_le_of_abs_lt {p : ℕ} {e : ℤ} {x : K} (hx : x ≠ 0)
    (h : |x| < (2 : K) ^ (e + p)) : ulpExp p x ≤ e := by
  have hlog := (Int.lt_zpow_iff_log_lt (b := 2) (by decide) (abs_pos.mpr hx)).mp
    (by simpa using h)
  unfold ulpExp
  omega

omit [FloorRing K] in
private theorem int_mul_zpow_on_grid (m : ℤ) {e g : ℤ} (h : g ≤ e) :
    ∃ n : ℤ, (m : K) * 2 ^ e = (n : K) * 2 ^ g := by
  refine ⟨m * 2 ^ (e - g).toNat, ?_⟩
  push_cast
  rw [mul_assoc, ← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr h),
    ← zpow_add₀ two_ne_zero, sub_add_cancel]

private theorem log_abs_mul_bounds {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    Int.log 2 |a| + Int.log 2 |b| ≤ Int.log 2 |a * b| ∧
      Int.log 2 |a * b| ≤ Int.log 2 |a| + Int.log 2 |b| + 1 := by
  have hlo (x : K) (hx : x ≠ 0) : (2 : K) ^ Int.log 2 |x| ≤ |x| := by
    simpa using Int.zpow_log_le_self (b := 2) (by decide) (abs_pos.mpr hx)
  have hhi (x : K) : |x| < (2 : K) ^ (Int.log 2 |x| + 1) := by
    simpa using Int.lt_zpow_succ_log_self (b := 2) (by decide) |x|
  have hab := abs_pos.mpr (mul_ne_zero ha hb)
  constructor
  · apply (Int.zpow_le_iff_le_log (b := 2) (by decide) hab).mp
    push_cast
    rw [abs_mul, zpow_add₀ two_ne_zero]
    exact mul_le_mul (hlo a ha) (hlo b hb) (two_zpow_pos _).le (abs_nonneg _)
  · have h : |a * b| < (2 : K) ^ ((Int.log 2 |a| + 1) + (Int.log 2 |b| + 1)) := by
      rw [abs_mul, zpow_add₀ two_ne_zero]
      exact mul_lt_mul_of_pos' (hhi a) (hhi b) (abs_pos.mpr hb) (two_zpow_pos _)
    have hlog := (Int.lt_zpow_iff_log_lt (b := 2) (by decide) hab).mp (by simpa using h)
    omega

private theorem ulpExp_le_of_isFloatIn_fl {p : ℕ} {qmin qmax : ℤ} {x : K} (hp : 1 ≤ p)
    (hx : x ≠ 0) (hf : IsFloatIn p qmin qmax (fl p x)) : ulpExp p x ≤ qmax := by
  let ℓ := ulpExp p x
  let y := x / (2 : K) ^ ℓ
  have hscaled : (2 : K) ^ (p - 1) ≤ |y| := (scaled_bounds hp hx).1
  -- Integer rounding cannot take the magnitude below the bottom of the input binade.
  have hrne : (2 : K) ^ (p - 1) ≤ |(rne y : K)| := by
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy] at hscaled
      have h : ((2 ^ (p - 1) : ℤ) : K) ≤ y := by exact_mod_cast hscaled
      have hr : (2 : K) ^ (p - 1) ≤ (rne y : K) := by exact_mod_cast le_rne_of_le h
      exact hr.trans (le_abs_self _)
    · rw [abs_of_nonpos hy] at hscaled
      have h : y ≤ ((-(2 ^ (p - 1)) : ℤ) : K) := by
        push_cast
        linarith only [hscaled]
      have hr : (rne y : K) ≤ -(2 : K) ^ (p - 1) := by exact_mod_cast rne_le_of_le h
      exact (show (2 : K) ^ (p - 1) ≤ -(rne y : K) by linarith only [hr]).trans (neg_le_abs _)
  have hlo : (2 : K) ^ Int.log 2 |x| ≤ |fl p x| := by
    have h : (2 : K) ^ (p - 1) * 2 ^ ℓ = 2 ^ Int.log 2 |x| := by
      rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
      congr 1
      dsimp [ℓ, ulpExp]
      rw [Nat.cast_sub hp, Nat.cast_one]
      omega
    rw [← h, fl, abs_mul, abs_of_pos (two_zpow_pos (K := K) ℓ)]
    exact mul_le_mul_of_nonneg_right hrne (two_zpow_pos ℓ).le
  obtain ⟨m, e, hm, -, he, hfl⟩ := hf
  have hhi : |fl p x| < (2 : K) ^ (qmax + p) := by
    rw [hfl]
    exact (abs_int_mul_zpow_lt_iff.mpr hm).trans_le
      (zpow_le_zpow_right₀ (by norm_num) (by omega))
  have hlog := (zpow_lt_zpow_iff_right₀ (show (1 : K) < 2 by norm_num)).mp (hlo.trans_lt hhi)
  unfold ulpExp
  omega

/-- **Error-free transformation of a product via fused multiply-add.** For nonzero bounded-format
floats `a` and `b`, let `π = fl p (a * b)` be the nearest-even rounded product. If `π` is finite in
that format and the sum of the operand log exponents is at least `qmin + 2 * (p - 1)` (equivalently,
`emin + p - 1`), then the exact residual `a * b - π` is in the format, including subnormals.
Consequently a single nearest-even rounding of the fused expression returns the residual unchanged,
and adding it to `π` in the underlying field gives `a * b` exactly.

Here `fl` models nearest-even rounding with unbounded exponents; the format-membership hypotheses
and conclusion are separate. In particular the unrounded product need not be at most the largest
finite value. The reconstruction is an exact sum of values, not another rounded operation. -/
public theorem fusedProductResidual {p : ℕ} {qmin qmax : ℤ} {a b : K} (hp : 1 ≤ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hfa : IsFloatIn p qmin qmax a) (hfb : IsFloatIn p qmin qmax b)
    (hlo : qmin + 2 * ((p : ℤ) - 1) ≤ Int.log 2 |a| + Int.log 2 |b|)
    (hπ : IsFloatIn p qmin qmax (fl p (a * b))) :
    let π := fl p (a * b)
    IsFloatIn p qmin qmax (a * b - π) ∧
      fl p (a * b - π) = a * b - π ∧ π + fl p (a * b - π) = a * b := by
  intro π
  set g := ulpExp p a + ulpExp p b with hg
  let ℓ := ulpExp p (a * b)
  have hab := mul_ne_zero ha hb
  obtain ⟨hlogLo, hlogHi⟩ := log_abs_mul_bounds ha hb
  have hgmin : qmin ≤ g := by rw [hg]; unfold ulpExp; omega
  have hgℓ : g ≤ ℓ := by rw [hg]; dsimp [ℓ, ulpExp]; omega
  have hℓgp : ℓ ≤ g + p := by rw [hg]; dsimp [ℓ, ulpExp]; omega
  have hgmax : g ≤ qmax := hgℓ.trans (ulpExp_le_of_isFloatIn_fl hp hab hπ)
  -- Re-express the operands on their respective last-place grids and the product on their sum.
  obtain ⟨ma, ea, hma, -, -, ham⟩ := hfa
  obtain ⟨mb, eb, hmb, -, -, hbm⟩ := hfb
  have hga : ulpExp p a ≤ ea :=
    ulpExp_le_of_abs_lt ha (ham ▸ abs_int_mul_zpow_lt_iff.mpr hma)
  have hgb : ulpExp p b ≤ eb :=
    ulpExp_le_of_abs_lt hb (hbm ▸ abs_int_mul_zpow_lt_iff.mpr hmb)
  obtain ⟨na, hna⟩ := int_mul_zpow_on_grid (K := K) ma hga
  obtain ⟨nb, hnb⟩ := int_mul_zpow_on_grid (K := K) mb hgb
  have hprod : a * b = ((na * nb : ℤ) : K) * 2 ^ g := calc
    a * b = ((na : K) * 2 ^ ulpExp p a) * ((nb : K) * 2 ^ ulpExp p b) :=
      congrArg₂ (· * ·) (ham.trans hna) (hbm.trans hnb)
    _ = _ := by rw [hg, zpow_add₀ two_ne_zero, Int.cast_mul]; ring
  obtain ⟨nπ, hnπ⟩ := int_mul_zpow_on_grid (K := K) (rne (a * b / 2 ^ ℓ)) hgℓ
  have hres : a * b - π = ((na * nb - nπ : ℤ) : K) * 2 ^ g := by
    change a * b - (rne (a * b / 2 ^ ℓ) : K) * 2 ^ ℓ = _
    rw [hnπ, hprod, Int.cast_sub, sub_mul]
  -- Half an ulp of the product is strictly smaller than `2^p` grid steps.
  have hmag : |a * b - π| < (2 : K) ^ (g + p) := calc
    |a * b - π| ≤ 1 / 2 * 2 ^ ℓ := by
      change |a * b - fl p (a * b)| ≤ _
      rw [abs_sub_comm, abs_fl_sub_eq]
      exact mul_le_mul_of_nonneg_right (abs_rne_sub_le_half _) (two_zpow_pos _).le
    _ < 2 ^ ℓ := by linarith [two_zpow_pos (K := K) ℓ]
    _ ≤ 2 ^ (g + p) := zpow_le_zpow_right₀ (by norm_num) hℓgp
  have hfres : IsFloatIn p qmin qmax (a * b - π) := by
    rw [hres] at hmag
    exact ⟨_, g, abs_int_mul_zpow_lt_iff.mp hmag, hgmin, hgmax, hres⟩
  have hexact := fl_eq_self hp hfres.isFloat
  exact ⟨hfres, hexact, by rw [hexact]; ring⟩

end Cslib.Algorithms.Lean.FloatingPoint

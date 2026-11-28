/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Numerical.FloatingPoint
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.LinearCombination

/-!
# Double rounding through an extended precision

Rounding an exact result first to `p'` bits and then to `p < p'` bits, as x87 hardware does with
`p' = 64` and `p = 53`, can differ from rounding it to `p` bits directly. In the model of
`Cslib.Algorithms.Lean.FloatingPoint` (radix 2, round to nearest with ties to even at both
precisions), double rounding of the basic operations is innocuous when `p'` is large enough
(Figueroa, *When is double rounding innocuous?*, SIGNUM Newsletter 30(3), 1995; Roux, *Innocuous
double rounding of basic arithmetic operations*, J. Formalized Reasoning 7(1), 2014,
Theorems 10, 20, 25 and 29, Table II). The proofs follow Roux's: double rounding can go wrong only
for an exact value within half a last place of `p'` bits of a midpoint of `p`-bit numbers, and
each operation either is exact at `p'` bits or stays far enough from the midpoints.

## Main results

* `fl_fl_eq_of_near`: double rounding of `z` is innocuous when `z` is a midpoint or lies within
  `1/2 - 2^(-d-1)` of a `p`-bit number, in units of its last place, where `d = p' - p ≥ 1`.
* `fl_fl_add`, `fl_fl_mul`, `fl_fl_div`, `fl_fl_sqrt`: with unbounded exponents, double rounding is
  innocuous for `+` (and `-`) if `p' ≥ 2p + 1`, for `×` and `/` if `p' ≥ 2p`, and for `√` if
  `p' ≥ 2p + 2`.
* `flIn_flIn_add`, `flIn_flIn_mul`, `flIn_flIn_div`, `flIn_flIn_sqrt`: with rounding in formats
  with gradual underflow (`flIn`), innocuous double rounding when the least exponents `q` and `q'`
  of the two formats also satisfy `q' ≤ q` for `+`, `q' ≤ 2q` for `×` and `q' ≤ q - p - 2` for `/`
  and `√`; `binary32_via_binary64` for IEEE binary32 operations evaluated in binary64. For `√`,
  Roux's Table II also allows the alternative condition `2q' ≤ q - 4p - 2`, which is not covered
  here.
* `innocuous_double_rounding`: these results, with the x87 example, counterexamples showing that
  the bounds on `p'` are optimal for `p ≥ 2` (`±` and `/`), `p ≥ 4` (`×`) and `p ≥ 1` (`√`)
  (after Roux's Remarks 11, 21, 26 and 30, which give them for `p = 4`), and one showing that the
  conditions on `q'` cannot simply be dropped.

## Cost model

None: these are statements about the values computed, not about the cost of computing them.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FloatingPoint

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-! ## Rounding to an integer -/

private theorem rne_eq_of_abs_sub_lt {m : K} {k : ℤ} (h : |m - k| < 1 / 2) : rne m = k := by
  have h₁ := abs_rne_sub_le m k
  rw [abs_sub_comm (k : K)] at h₁
  have h₂ : |((rne m - k : ℤ) : K)| < 1 := by
    push_cast
    calc |(rne m : K) - k| = |((rne m : K) - m) + (m - k)| := by ring_nf
      _ ≤ |(rne m : K) - m| + |m - k| := abs_add_le _ _
      _ < 1 := by linarith
  have h₃ : |rne m - k| < 1 := by
    have : ((|rne m - k| : ℤ) : K) < 1 := by rwa [Int.cast_abs]
    exact_mod_cast this
  rw [abs_lt] at h₃
  omega

private theorem rne_intCast_add_half_of_even {k : ℤ} (hk : Even k) : rne ((k : K) + 1 / 2) = k := by
  have hf : ⌊(k : K) + 1 / 2⌋ = k := by
    rw [Int.floor_eq_iff]
    constructor <;> linarith
  unfold rne
  rw [hf]
  simp [hk]

private theorem rne_intCast_add_half_of_odd {k : ℤ} (hk : Odd k) :
    rne ((k : K) + 1 / 2) = k + 1 := by
  have hf : ⌊(k : K) + 1 / 2⌋ = k := by
    rw [Int.floor_eq_iff]
    constructor <;> linarith
  unfold rne
  rw [hf]
  simp [Int.not_even_iff_odd.2 hk]

private theorem abs_rne_le_of_abs_le {m : K} {n : ℤ} (h : |m| ≤ n) : |rne m| ≤ n := by
  rw [abs_le] at h ⊢
  exact ⟨le_rne_of_le (by push_cast; linarith), rne_le_of_le h.2⟩

private theorem le_abs_rne_of_le_abs {m : K} {n : ℤ} (hn : 0 ≤ n) (h : (n : K) ≤ |m|) :
    n ≤ |rne m| := by
  rcases le_or_gt 0 m with hm | hm
  · rw [abs_of_nonneg hm] at h
    have := le_rne_of_le h
    rw [abs_of_nonneg (by omega)]
    exact this
  · rw [abs_of_neg hm] at h
    have := rne_le_of_le (m := m) (k := -n) (by push_cast; linarith)
    rw [abs_of_nonpos (by omega)]
    omega

/-! ## Rounding at a known exponent -/

variable {p : ℕ}

private theorem le_ulpExp_of_le_abs (hp : 1 ≤ p) {x : K} {e : ℤ}
    (h : (2 : K) ^ (p - 1) * 2 ^ e ≤ |x|) : e ≤ ulpExp p x := by
  have hax : 0 < |x| := lt_of_lt_of_le (by positivity) h
  have h' : (2 : K) ^ (e + ((p : ℤ) - 1)) ≤ |x| := by
    rw [zpow_add₀ two_ne_zero, mul_comm, show ((p : ℤ) - 1) = ((p - 1 : ℕ) : ℤ) by omega,
      zpow_natCast]
    exact h
  have hl : e + ((p : ℤ) - 1) ≤ Int.log 2 |x| :=
    (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hax).1 (by exact_mod_cast h')
  unfold ulpExp
  omega

private theorem ulpExp_le_of_abs_lt {x : K} (hx : x ≠ 0) {e : ℤ} (h : |x| < 2 ^ p * 2 ^ e) :
    ulpExp p x ≤ e := by
  have hax : 0 < |x| := abs_pos.2 hx
  have h' : |x| < (2 : K) ^ (e + p) := by
    rw [zpow_add₀ two_ne_zero, mul_comm, zpow_natCast]
    exact h
  have hl : Int.log 2 |x| < e + p :=
    (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hax).1 (by exact_mod_cast h')
  unfold ulpExp
  omega

private theorem ulpExp_eq_of_le_of_lt (hp : 1 ≤ p) {x : K} {e : ℤ}
    (h₁ : (2 : K) ^ (p - 1) * 2 ^ e ≤ |x|)
    (h₂ : |x| < 2 ^ p * 2 ^ e) : ulpExp p x = e :=
  le_antisymm (ulpExp_le_of_abs_lt (abs_pos.1 (lt_of_lt_of_le (by positivity) h₁)) h₂)
    (le_ulpExp_of_le_abs hp h₁)

private theorem isFloat_of_abs_eq (hp : 1 ≤ p) {x : K} {e : ℤ} (h : |x| = 2 ^ p * 2 ^ e) :
    IsFloat p x := by
  have h2 : (2 : ℤ) ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ', Nat.sub_add_cancel hp]
  have hlt : |(2 : ℤ) ^ (p - 1)| < 2 ^ p := by
    rw [abs_of_pos (by positivity), h2]
    have : (0 : ℤ) < 2 ^ (p - 1) := by positivity
    omega
  have hval : (2 : K) ^ p * 2 ^ e = ((2 ^ (p - 1) : ℤ) : K) * 2 ^ (e + 1) := by
    rw [zpow_add_one₀ two_ne_zero]
    push_cast
    rw [show (2 : K) ^ p = 2 * 2 ^ (p - 1) by rw [← pow_succ', Nat.sub_add_cancel hp]]
    ring
  rcases abs_eq (by positivity) |>.1 h with h' | h'
  · exact ⟨_, _, hlt, by rw [h', hval]⟩
  · refine ⟨-2 ^ (p - 1), e + 1, by rwa [abs_neg], ?_⟩
    rw [h', hval]
    push_cast
    ring

private theorem fl_eq_of_le_of_le (hp : 1 ≤ p) {x : K} {e : ℤ}
    (h₁ : (2 : K) ^ (p - 1) * 2 ^ e ≤ |x|)
    (h₂ : |x| ≤ 2 ^ p * 2 ^ e) : fl p x = rne (x / 2 ^ e) * 2 ^ e := by
  rcases h₂.lt_or_eq with h₂ | h₂
  · rw [fl, ulpExp_eq_of_le_of_lt hp h₁ h₂]
  · have he : (0 : K) < 2 ^ e := by positivity
    rw [fl_eq_self hp (isFloat_of_abs_eq hp h₂)]
    -- `x / 2^e = ± 2^p` is an integer
    obtain ⟨k, hk⟩ : ∃ k : ℤ, x / 2 ^ e = k := by
      rcases abs_eq (by positivity) |>.1 h₂ with h' | h'
      · exact ⟨2 ^ p, by rw [h', mul_div_cancel_right₀ _ he.ne']; push_cast; rfl⟩
      · exact ⟨-2 ^ p, by rw [h', neg_div, mul_div_cancel_right₀ _ he.ne']; push_cast; rfl⟩
    rw [hk, rne_intCast, ← hk, div_mul_cancel₀ _ he.ne']

/-! ## The double-rounding criterion -/

/- Rounding `M · 2^d` to an integer, dividing by `2^d` and rounding again gives `rne M` when `M` is
a half-integer or lies within `1/2 - 2^(-d-1)` of an integer. -/
private theorem rne_rne_mul_two_pow_div {d : ℕ} (hd : 1 ≤ d) {M : K}
    (h : (∃ k : ℤ, M = k + 1 / 2) ∨ ∃ k : ℤ, |M - k| < 1 / 2 - 1 / 2 ^ (d + 1)) :
    rne ((rne (M * 2 ^ d) : K) / 2 ^ d) = rne M := by
  have hD : (0 : K) < 2 ^ d := by positivity
  rcases h with ⟨k, rfl⟩ | ⟨k, hk⟩
  · have hint : ((k : K) + 1 / 2) * 2 ^ d = ((k * 2 ^ d + 2 ^ (d - 1) : ℤ) : K) := by
      push_cast
      rw [show (2 : K) ^ d = 2 * 2 ^ (d - 1) by rw [← pow_succ', Nat.sub_add_cancel hd]]
      ring
    rw [hint, rne_intCast, ← hint, mul_div_cancel_right₀ _ hD.ne']
  · have hpos : (0 : K) < 1 / 2 ^ (d + 1) := by positivity
    rw [rne_eq_of_abs_sub_lt (m := M) (k := k) (by linarith)]
    apply rne_eq_of_abs_sub_lt
    have h₁ := abs_rne_sub_le_half (M * 2 ^ d)
    have h₂ : |M * 2 ^ d - k * 2 ^ d| < 2 ^ d / 2 - 1 / 2 := by
      rw [← sub_mul, abs_mul, abs_of_pos hD]
      calc |M - k| * 2 ^ d < (1 / 2 - 1 / 2 ^ (d + 1)) * 2 ^ d :=
            mul_lt_mul_of_pos_right hk hD
        _ = 2 ^ d / 2 - 1 / 2 := by rw [pow_succ]; field_simp
    have h₃ : |(rne (M * 2 ^ d) : K) - k * 2 ^ d| < 2 ^ d / 2 := by
      calc |(rne (M * 2 ^ d) : K) - k * 2 ^ d|
          = |((rne (M * 2 ^ d) : K) - M * 2 ^ d) + (M * 2 ^ d - k * 2 ^ d)| := by ring_nf
        _ ≤ |(rne (M * 2 ^ d) : K) - M * 2 ^ d| + |M * 2 ^ d - k * 2 ^ d| := abs_add_le _ _
        _ < 2 ^ d / 2 := by linarith
    have h₄ : (rne (M * 2 ^ d) : K) / 2 ^ d - k = ((rne (M * 2 ^ d) : K) - k * 2 ^ d) / 2 ^ d := by
      field_simp
    rw [h₄, abs_div, abs_of_pos hD, div_lt_iff₀ hD]
    linarith

private theorem mid_or_near_of_floor {d : ℕ} {M : K}
    (h : M ≠ ⌊M⌋ + 1 / 2 → 1 / 2 ^ (d + 1) < |M - (⌊M⌋ + 1 / 2)|) :
    (∃ k : ℤ, M = k + 1 / 2) ∨ ∃ k : ℤ, |M - k| < 1 / 2 - 1 / 2 ^ (d + 1) := by
  by_cases hM : M = ⌊M⌋ + 1 / 2
  · exact Or.inl ⟨⌊M⌋, hM⟩
  right
  have h1 := h hM
  have h2 := Int.floor_le M
  have h3 := Int.lt_floor_add_one M
  rcases lt_or_gt_of_ne hM with h4 | h4
  · refine ⟨⌊M⌋, ?_⟩
    rw [abs_of_neg (by linarith)] at h1
    rw [abs_of_nonneg (by linarith)]
    linarith
  · refine ⟨⌊M⌋ + 1, ?_⟩
    rw [abs_of_pos (by linarith)] at h1
    push_cast
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- **Double rounding is innocuous away from midpoints.** Let $K$ be a linearly ordered field with
a floor function, let $p \ge 1$ and $d \ge 1$ be natural numbers, let $z \in K$, and let
$M = z / 2^e$, where $e$ is the exponent of the last place of $z$ at precision $p$. If $M$ is a
half-integer, or $|M - k| < 1/2 - 2^{-d-1}$ for some integer $k$, then rounding $z$ to nearest,
ties to even, first with $p + d$ bits and then with $p$ bits gives the same as rounding it directly
with $p$ bits: $\mathrm{fl}_p(\mathrm{fl}_{p+d}(z)) = \mathrm{fl}_p(z)$.

In other words, double rounding can differ from direct rounding only when $z$ is not a midpoint of
consecutive $p$-bit floating-point numbers but lies within half a last place of $p + d$ bits of
one. -/
theorem fl_fl_eq_of_near (hp : 1 ≤ p) {d : ℕ} (hd : 1 ≤ d) {z : K}
    (h : (∃ k : ℤ, z / 2 ^ ulpExp p z = k + 1 / 2) ∨
      ∃ k : ℤ, |z / 2 ^ ulpExp p z - k| < 1 / 2 - 1 / 2 ^ (d + 1)) :
    fl p (fl (p + d) z) = fl p z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [fl_zero]
  have hE : (0 : K) < 2 ^ ulpExp p z := two_zpow_pos _
  have hD : (0 : K) < 2 ^ d := by positivity
  have he' : ulpExp (p + d) z = ulpExp p z - d := by
    unfold ulpExp
    push_cast
    ring
  obtain ⟨hM₁, hM₂⟩ := scaled_bounds hp hz
  have hfl : fl (p + d) z = (rne (z / 2 ^ ulpExp p z * 2 ^ d) : K) / 2 ^ d * 2 ^ ulpExp p z := by
    have hz' : z / 2 ^ (ulpExp p z - d) = z / 2 ^ ulpExp p z * 2 ^ d := by
      rw [zpow_sub₀ two_ne_zero, zpow_natCast]
      field_simp
    rw [fl, he', hz', zpow_sub₀ two_ne_zero, zpow_natCast]
    field_simp
  set M := z / 2 ^ ulpExp p z with hM_def
  set r := rne (M * 2 ^ d) with hr_def
  have hr₁ : (2 : ℤ) ^ (p + d - 1) ≤ |r| := by
    apply le_abs_rne_of_le_abs (by positivity)
    rw [abs_mul, abs_of_pos hD]
    push_cast
    calc (2 : K) ^ (p + d - 1) = 2 ^ (p - 1) * 2 ^ d := by rw [← pow_add]; congr 1; omega
      _ ≤ |M| * 2 ^ d := by gcongr
  have hr₂ : |r| ≤ (2 : ℤ) ^ (p + d) := by
    apply abs_rne_le_of_abs_le
    rw [abs_mul, abs_of_pos hD]
    push_cast
    rw [pow_add]
    exact (mul_lt_mul_of_pos_right hM₂ hD).le
  have hr₁' : (2 : K) ^ (p - 1) * 2 ^ d ≤ |(r : K)| := by
    rw [← pow_add, show p - 1 + d = p + d - 1 by omega, ← Int.cast_abs]
    exact_mod_cast hr₁
  have hr₂' : |(r : K)| ≤ 2 ^ p * 2 ^ d := by
    rw [← pow_add, ← Int.cast_abs]
    exact_mod_cast hr₂
  have hw₁ : (2 : K) ^ (p - 1) * 2 ^ ulpExp p z ≤ |(r : K) / 2 ^ d * 2 ^ ulpExp p z| := by
    rw [abs_mul, abs_div, abs_of_pos hD, abs_of_pos hE]
    gcongr
    rw [le_div_iff₀ hD]
    exact hr₁'
  have hw₂ : |(r : K) / 2 ^ d * 2 ^ ulpExp p z| ≤ 2 ^ p * 2 ^ ulpExp p z := by
    rw [abs_mul, abs_div, abs_of_pos hD, abs_of_pos hE]
    gcongr
    rw [div_le_iff₀ hD]
    exact hr₂'
  rw [hfl, fl_eq_of_le_of_le hp hw₁ hw₂, mul_div_cancel_right₀ _ hE.ne', hr_def,
    rne_rne_mul_two_pow_div hd h]
  rfl

/-! ## Midpoint distances of the four operations -/

omit [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K] in
private theorem IsFloat.neg {x : K} (hx : IsFloat p x) : IsFloat p (-x) := by
  obtain ⟨m, e, hm, rfl⟩ := hx
  exact ⟨-m, e, by rwa [abs_neg], by push_cast; ring⟩

private theorem IsFloat.exists_normalized (hp : 1 ≤ p) {x : K} (hx : IsFloat p x) (hx0 : x ≠ 0) :
    ∃ m e : ℤ, 2 ^ (p - 1) ≤ |m| ∧ |m| < 2 ^ p ∧ x = m * 2 ^ e := by
  have hfl : (rne (x / 2 ^ ulpExp p x) : K) * 2 ^ ulpExp p x = x := fl_eq_self hp hx
  have hM : (rne (x / 2 ^ ulpExp p x) : K) = x / 2 ^ ulpExp p x := by
    rw [eq_div_iff (two_zpow_pos _).ne']
    exact hfl
  obtain ⟨h₁, h₂⟩ := scaled_bounds hp hx0
  rw [← hM, ← Int.cast_abs] at h₁ h₂
  exact ⟨_, _, by exact_mod_cast h₁, by exact_mod_cast h₂, hfl.symm⟩

omit [IsStrictOrderedRing K] in
private theorem exists_int_mul_of_add {mx my ex ey g : ℤ} (hx : g ≤ ex) (hy : g ≤ ey) :
    ∃ k : ℤ, (mx : K) * 2 ^ ex + my * 2 ^ ey = k * 2 ^ g := by
  refine ⟨mx * 2 ^ (ex - g).toNat + my * 2 ^ (ey - g).toNat, ?_⟩
  push_cast
  rw [add_mul, mul_assoc, mul_assoc, ← zpow_natCast, ← zpow_natCast,
    ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero, Int.toNat_of_nonneg (by omega),
    Int.toNat_of_nonneg (by omega)]
  ring_nf

private theorem abs_lt_of_eq_int_mul {k g : ℤ} {n : ℕ} {z : K} (hk : z = k * 2 ^ g)
    (h : |z| < 2 ^ n * 2 ^ g) : |k| < 2 ^ n := by
  rw [hk, abs_mul, abs_of_pos (two_zpow_pos (K := K) g)] at h
  have h' := lt_of_mul_lt_mul_right h (two_zpow_pos (K := K) g).le
  rw [← Int.cast_abs] at h'
  exact_mod_cast h'

/- When the smaller operand of a sum lies below the last place of `p + d` bits, the sum is
within `1/2 - 2^(-d-1)` of a `p`-bit number, at the scale of its last place. -/
private theorem exists_abs_sub_lt_of_add (hp : 1 ≤ p) {d : ℕ} (hd : p + 1 ≤ d) {mx my ex ey : ℤ}
    (hmx : |mx| < 2 ^ p) (hmy : |my| < 2 ^ p) {z : K}
    (hz_def : z = mx * 2 ^ ex + my * 2 ^ ey) (hz : z ≠ 0) (hey : ey < ulpExp p z - d) :
    ∃ k : ℤ, |z / 2 ^ ulpExp p z - k| < 1 / 2 - 1 / 2 ^ (d + 1) := by
  set e := ulpExp p z with he_def
  have hE : (0 : K) < 2 ^ e := two_zpow_pos e
  obtain ⟨hM₁, -⟩ := scaled_bounds hp hz
  rw [← he_def, abs_div, abs_of_pos hE, le_div_iff₀ hE] at hM₁
  have hmx' : |(mx : K)| ≤ 2 ^ p - 1 := by
    have : |mx| ≤ 2 ^ p - 1 := by omega
    rw [← Int.cast_abs]
    exact_mod_cast this
  have hmy' : |(my : K)| ≤ 2 ^ p - 1 := by
    have : |my| ≤ 2 ^ p - 1 := by omega
    rw [← Int.cast_abs]
    exact_mod_cast this
  have hP : (1 : K) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
  have hey' : (2 : K) ^ ey ≤ 2 ^ e / 2 ^ (d + 1) := by
    rw [← zpow_natCast, ← zpow_sub₀ two_ne_zero]
    exact zpow_le_zpow_right₀ (by norm_num) (by push_cast; omega)
  have hD : (2 : K) ^ (d + 1) = 4 * 2 ^ (d - 1) := by
    rw [show d + 1 = (d - 1) + 2 by omega, pow_add]
    ring
  have hPD : (2 : K) ^ p ≤ 2 ^ (d - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  set t : K := 2 ^ e / 2 ^ (d + 1) with ht_def
  have ht0 : 0 < t := by positivity
  have ht : (2 : K) ^ p * t ≤ 2 ^ e / 4 := by
    rw [ht_def, hD, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hsmall : |(my : K) * 2 ^ ey| ≤ 2 ^ p * t - t := by
    rw [abs_mul, abs_of_pos (two_zpow_pos (K := K) ey)]
    calc |(my : K)| * 2 ^ ey ≤ (2 ^ p - 1) * t :=
          mul_le_mul hmy' hey' (two_zpow_pos ey).le (by linarith)
      _ = 2 ^ p * t - t := by ring
  -- the larger operand is a multiple of the last place of `z`
  have hxe : e ≤ ex := by
    by_contra hcon
    push Not at hcon
    have hx2 : (2 : K) ^ ex ≤ 2 ^ e / 2 := by
      have : (2 : K) ^ e / 2 = 2 ^ (e - 1) := by
        rw [zpow_sub_one₀ two_ne_zero, div_eq_mul_inv]
      rw [this]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hbig : |(mx : K) * 2 ^ ex| ≤ 2 ^ p * (2 ^ e / 2) - 2 ^ e / 2 := by
      rw [abs_mul, abs_of_pos (two_zpow_pos (K := K) ex)]
      calc |(mx : K)| * 2 ^ ex ≤ (2 ^ p - 1) * (2 ^ e / 2) :=
            mul_le_mul hmx' hx2 (two_zpow_pos ex).le (by linarith)
        _ = 2 ^ p * (2 ^ e / 2) - 2 ^ e / 2 := by ring
    have := abs_add_le ((mx : K) * 2 ^ ex) (my * 2 ^ ey)
    rw [← hz_def] at this
    have h2 : (2 : K) ^ p * (2 ^ e / 2) = 2 ^ (p - 1) * 2 ^ e := by
      rw [show (2 : K) ^ p = 2 * 2 ^ (p - 1) by rw [← pow_succ', Nat.sub_add_cancel hp]]
      ring
    linarith
  refine ⟨mx * 2 ^ (ex - e).toNat, ?_⟩
  have hdiff : z / 2 ^ e - ((mx * 2 ^ (ex - e).toNat : ℤ) : K) = my * 2 ^ ey / 2 ^ e := by
    push_cast
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_sub₀ two_ne_zero, hz_def]
    field_simp
    ring
  rw [hdiff, abs_div, abs_of_pos hE, div_lt_iff₀ hE]
  have : (1 / 2 - 1 / 2 ^ (d + 1)) * (2 : K) ^ e = 2 ^ e / 2 - t := by
    rw [ht_def]
    ring
  rw [this]
  linarith

/- A quotient of `p`-bit numbers that is not a midpoint at the scale `2^e` lies farther than
`2^(-p-t)` from it, as soon as it is at least `2^(-t)` at that scale. -/
private theorem forall_far_of_div (hp : 1 ≤ p) {t : ℕ} (ht : 1 ≤ t) {x y : K} (hx : IsFloat p x)
    (hy : IsFloat p y) {e : ℤ} (hM : 1 / 2 ^ t ≤ |x / y / 2 ^ e|) (n : ℤ)
    (hn : x / y / 2 ^ e ≠ n + 1 / 2) : 1 / 2 ^ (p + t) < |x / y / 2 ^ e - (n + 1 / 2)| := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp only [div_zero, zero_div, abs_zero] at hM
    exact absurd hM (not_le.2 (by positivity))
  obtain ⟨mx, ex, hmx, rfl⟩ := hx
  obtain ⟨my, ey, hmy₁, hmy₂, rfl⟩ := hy.exists_normalized hp hy0
  have hmy₁' : (2 : K) ^ (p - 1) ≤ |(my : K)| := by rw [← Int.cast_abs]; exact_mod_cast hmy₁
  have hmy₂' : |(my : K)| < 2 ^ p := by rw [← Int.cast_abs]; exact_mod_cast hmy₂
  have hmx' : |(mx : K)| < 2 ^ p := by rw [← Int.cast_abs]; exact_mod_cast hmx
  have hmy0 : (0 : K) < |(my : K)| := lt_of_lt_of_le (by positivity) hmy₁'
  have hmyK : (my : K) ≠ 0 := abs_pos.1 hmy0
  have hMeq : (mx : K) * 2 ^ ex / (my * 2 ^ ey) / 2 ^ e = mx * 2 ^ (ex - ey - e) / my := by
    rw [zpow_sub₀ two_ne_zero, zpow_sub₀ two_ne_zero]
    field_simp
  rw [hMeq] at hM hn ⊢
  -- the exponent `ex - ey - e` is at least `-t`
  have hs : -(t : ℤ) ≤ ex - ey - e := by
    by_contra hs
    push Not at hs
    have h2 : (2 : K) ^ (ex - ey - e) ≤ 1 / 2 ^ t / 2 := by
      rw [div_div, ← pow_succ, one_div, ← zpow_natCast, ← zpow_neg]
      exact zpow_le_zpow_right₀ (by norm_num) (by push_cast; omega)
    have h3 : |(mx : K) * 2 ^ (ex - ey - e) / my| < 1 / 2 ^ t := by
      rw [abs_div, abs_mul, abs_of_pos (two_zpow_pos (K := K) _), div_lt_iff₀ hmy0]
      have h4 : (2 : K) ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ', Nat.sub_add_cancel hp]
      calc |(mx : K)| * 2 ^ (ex - ey - e) ≤ |(mx : K)| * (1 / 2 ^ t / 2) :=
            mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ < 2 ^ p * (1 / 2 ^ t / 2) := mul_lt_mul_of_pos_right hmx' (by positivity)
        _ = 1 / 2 ^ t * 2 ^ (p - 1) := by rw [h4]; ring
        _ ≤ 1 / 2 ^ t * |(my : K)| := mul_le_mul_of_nonneg_left hmy₁' (by positivity)
    linarith
  -- so `2^t` times the quotient is an integer over `my`
  set N : ℤ := mx * 2 ^ (ex - ey - e + t).toNat with hN
  have hNK : (mx : K) * 2 ^ (ex - ey - e) = N / 2 ^ t := by
    rw [hN, eq_div_iff (by positivity)]
    push_cast
    rw [mul_assoc, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ two_ne_zero,
      Int.toNat_of_nonneg (by omega)]
  rw [hNK] at hn ⊢
  have h2t : (2 : K) ^ t = 2 * 2 ^ (t - 1) := by rw [← pow_succ', Nat.sub_add_cancel ht]
  set A : ℤ := N - 2 ^ (t - 1) * (2 * n + 1) * my with hA_def
  have hA : A ≠ 0 := by
    intro hA
    apply hn
    have : (A : K) = 0 := by exact_mod_cast hA
    rw [hA_def] at this
    push_cast at this
    rw [div_div, div_eq_iff (by positivity), h2t]
    linear_combination this
  have hA1 : (1 : K) ≤ |(A : K)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hA
  have hdiff : (N : K) / 2 ^ t / my - (n + 1 / 2) = (A : K) / (2 ^ t * my) := by
    rw [hA_def]
    push_cast
    rw [h2t]
    field_simp
  rw [hdiff, abs_div, abs_mul, abs_of_pos (by positivity : (0 : K) < 2 ^ t),
    lt_div_iff₀ (by positivity)]
  calc 1 / 2 ^ (p + t) * (2 ^ t * |(my : K)|) < 1 / 2 ^ (p + t) * (2 ^ t * 2 ^ p) := by
        gcongr
    _ = 1 := by rw [← pow_add, add_comm t p]; field_simp
    _ ≤ |(A : K)| := hA1

/- The square root of a `p`-bit number, at a scale `2^e` where it lies in `[7/16, 2^p)`, is a
midpoint or lies farther than `2^(-p-3)` from the nearest one. -/
private theorem far_of_sqrt (hp : 1 ≤ p) {x : ℝ} (hx : IsFloat p x) {e : ℤ}
    (h₁ : 7 / 16 ≤ √x / 2 ^ e)
    (h₂ : √x / 2 ^ e < 2 ^ p) (hn : √x / 2 ^ e ≠ ⌊√x / 2 ^ e⌋ + 1 / 2) :
    1 / 2 ^ (p + 3) < |√x / 2 ^ e - (⌊√x / 2 ^ e⌋ + 1 / 2)| := by
  have hE : (0 : ℝ) < 2 ^ e := two_zpow_pos e
  have hx0 : 0 < x := by
    by_contra hx0
    push Not at hx0
    rw [Real.sqrt_eq_zero'.2 hx0, zero_div] at h₁
    norm_num at h₁
  obtain ⟨mx, ex, hmx₁, hmx₂, rfl⟩ := hx.exists_normalized hp hx0.ne'
  have hmx0 : 0 < mx := by
    have : (0 : ℝ) < mx := pos_of_mul_pos_left hx0 (two_zpow_pos ex).le
    exact_mod_cast this
  have hmxK : (mx : ℝ) < 2 ^ p := by
    have : (mx : ℝ) = |(mx : ℝ)| := (abs_of_pos (by exact_mod_cast hmx0)).symm
    rw [this, ← Int.cast_abs]
    exact_mod_cast hmx₂
  set M := √((mx : ℝ) * 2 ^ ex) / 2 ^ e with hM_def
  set n := ⌊M⌋ with hn_def
  have hM0 : 0 < M := by linarith
  have hMsq : M ^ 2 = mx * 2 ^ (ex - 2 * e) := by
    rw [hM_def, div_pow, Real.sq_sqrt hx0.le, zpow_sub₀ two_ne_zero, ← zpow_natCast,
      ← zpow_mul]
    push_cast
    field_simp
    ring_nf
  have hfl₁ : (n : ℝ) ≤ M := Int.floor_le M
  have hfl₂ : M < n + 1 := Int.lt_floor_add_one M
  have hn0 : (0 : ℝ) ≤ n := by
    have : 0 ≤ n := Int.floor_nonneg.2 hM0.le
    exact_mod_cast this
  have hnp : (n : ℝ) + 1 / 2 < 2 ^ p := by
    have : n < 2 ^ p := by
      have : (n : ℝ) < 2 ^ p := lt_of_le_of_lt hfl₁ h₂
      exact_mod_cast this
    have : n + 1 ≤ 2 ^ p := by omega
    have : (n : ℝ) + 1 ≤ 2 ^ p := by exact_mod_cast this
    linarith
  have hsum : 0 < M + (n + 1 / 2) := by linarith
  have hprod : |M - (n + 1 / 2)| * (M + (n + 1 / 2)) = |M ^ 2 - (n + 1 / 2) ^ 2| := by
    rw [show M ^ 2 - (n + 1 / 2) ^ 2 = (M - (n + 1 / 2)) * (M + (n + 1 / 2)) by ring, abs_mul,
      abs_of_pos hsum]
  have hne : M ^ 2 ≠ (n + 1 / 2) ^ 2 := by
    intro h
    apply hn
    have := (sq_eq_sq₀ hM0.le (by linarith)).1 h
    exact this
  rcases le_or_gt (-2) (ex - 2 * e) with hs | hs
  · -- `4 M²` is an integer, so `|M² - (n + 1/2)²| ≥ 1/4`
    set N : ℤ := mx * 2 ^ (ex - 2 * e + 2).toNat with hN
    have hNK : 4 * M ^ 2 = N := by
      rw [hMsq, hN]
      push_cast
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_add₀ two_ne_zero]
      norm_num
      ring
    have hdiff : M ^ 2 - (n + 1 / 2) ^ 2 = ((N - (2 * n + 1) ^ 2 : ℤ) : ℝ) / 4 := by
      push_cast
      linear_combination hNK / 4
    have hA : N - (2 * n + 1) ^ 2 ≠ 0 := by
      intro hA
      apply hne
      have : ((N - (2 * n + 1) ^ 2 : ℤ) : ℝ) = 0 := by exact_mod_cast hA
      rw [this, zero_div] at hdiff
      linarith
    have hA1 : (1 : ℝ) ≤ |((N - (2 * n + 1) ^ 2 : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hA
    have hMh : M + (n + 1 / 2) < 2 ^ (p + 1) := by
      rw [pow_succ]
      linarith
    by_contra hcon
    push Not at hcon
    have h₃ : |M - (n + 1 / 2)| * (M + (n + 1 / 2)) < 1 / 2 ^ (p + 3) * 2 ^ (p + 1) := by
      calc |M - (n + 1 / 2)| * (M + (n + 1 / 2)) ≤ 1 / 2 ^ (p + 3) * (M + (n + 1 / 2)) :=
            mul_le_mul_of_nonneg_right hcon hsum.le
        _ < 1 / 2 ^ (p + 3) * 2 ^ (p + 1) := mul_lt_mul_of_pos_left hMh (by positivity)
    have h₄ : 1 / 2 ^ (p + 3) * (2 : ℝ) ^ (p + 1) = 1 / 4 := by
      rw [show p + 3 = (p + 1) + 2 by ring, pow_add]
      field_simp
      norm_num
    rw [hprod, hdiff, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4), h₄] at h₃
    linarith
  · -- `M² - (n + 1/2)²` is a nonzero integer multiple of `2^(ex - 2e)`, and `M ≥ 7/16`
    set A : ℤ := mx - (2 * n + 1) ^ 2 * 2 ^ (-(ex - 2 * e) - 2).toNat with hA_def
    have h4 : (2 : ℝ) ^ (-(ex - 2 * e) - 2).toNat * 2 ^ (ex - 2 * e) = 1 / 4 := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_add₀ two_ne_zero,
        show -(ex - 2 * e) - 2 + (ex - 2 * e) = -2 by ring]
      norm_num
    have hdiff : M ^ 2 - (n + 1 / 2) ^ 2 = A * 2 ^ (ex - 2 * e) := by
      rw [hMsq, hA_def]
      push_cast
      linear_combination (2 * (n : ℝ) + 1) ^ 2 * h4
    have hA : A ≠ 0 := by
      intro hA
      apply hne
      have : (A : ℝ) = 0 := by exact_mod_cast hA
      rw [this, zero_mul] at hdiff
      linarith
    have hA1 : (1 : ℝ) ≤ |(A : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hA
    have hS : (0 : ℝ) < 2 ^ (ex - 2 * e) := two_zpow_pos _
    have hMsq' : M ^ 2 < 2 ^ p * 2 ^ (ex - 2 * e) := by
      rw [hMsq]
      exact mul_lt_mul_of_pos_right hmxK hS
    have hbig : M + (n + 1 / 2) < 2 ^ (p + 3) * 2 ^ (ex - 2 * e) := by
      have : (2 : ℝ) ^ (p + 3) = 8 * 2 ^ p := by rw [pow_add]; norm_num; ring
      rw [this]
      nlinarith
    by_contra hcon
    push Not at hcon
    have h₃ : |M - (n + 1 / 2)| * (M + (n + 1 / 2)) < 2 ^ (ex - 2 * e) := by
      calc |M - (n + 1 / 2)| * (M + (n + 1 / 2)) ≤ 1 / 2 ^ (p + 3) * (M + (n + 1 / 2)) :=
            mul_le_mul_of_nonneg_right hcon hsum.le
        _ < 1 / 2 ^ (p + 3) * (2 ^ (p + 3) * 2 ^ (ex - 2 * e)) :=
            mul_lt_mul_of_pos_left hbig (by positivity)
        _ = 2 ^ (ex - 2 * e) := by field_simp
    rw [hprod, hdiff, abs_mul, abs_of_pos hS] at h₃
    nlinarith

/-! ## Innocuous double rounding of the four operations -/

private theorem fl_fl_add_aux (hp : 1 ≤ p) {d : ℕ} (hd : p + 1 ≤ d) {mx my ex ey : ℤ}
    (hmx : |mx| < 2 ^ p) (hmy : |my| < 2 ^ p) (hle : ey ≤ ex) :
    fl p (fl (p + d) ((mx : K) * 2 ^ ex + my * 2 ^ ey)) =
      fl p ((mx : K) * 2 ^ ex + my * 2 ^ ey) := by
  set z : K := mx * 2 ^ ex + my * 2 ^ ey with hz_def
  rcases eq_or_ne z 0 with hz | hz
  · rw [hz, fl_zero, fl_zero]
  by_cases hex : ulpExp p z - d ≤ ey
  · -- the sum is exact at precision `p + d`
    obtain ⟨k, hk⟩ := exists_int_mul_of_add (K := K) (mx := mx) (my := my) (ex := ex) (ey := ey)
      (by omega) hex
    rw [← hz_def] at hk
    have hkabs : |k| < 2 ^ (p + d) := by
      refine abs_lt_of_eq_int_mul hk ?_
      obtain ⟨-, h₂⟩ := scaled_bounds hp hz
      rw [abs_div, abs_of_pos (two_zpow_pos (K := K) _), div_lt_iff₀ (two_zpow_pos _)] at h₂
      rw [zpow_sub₀ two_ne_zero, zpow_natCast, pow_add]
      calc |z| < 2 ^ p * 2 ^ ulpExp p z := h₂
        _ = 2 ^ p * 2 ^ d * (2 ^ ulpExp p z / 2 ^ d) := by field_simp
    rw [fl_eq_self (by omega) ⟨k, _, hkabs, hk⟩]
  · exact fl_fl_eq_of_near hp (by omega)
      (Or.inr (exists_abs_sub_lt_of_add hp hd hmx hmy hz_def hz (by omega)))

/-- **Innocuous double rounding of sums.** Let $K$ be a linearly ordered field with a floor function
and let $p \ge 1$ and $p' \ge 2p + 1$ be natural numbers. For all binary floating-point numbers
$x, y \in K$ with $p$-bit significands and unbounded exponent, rounding $x + y$ to nearest, ties to
even, first with $p'$ bits and then with $p$ bits gives the same as rounding it directly with $p$
bits: $\mathrm{fl}_p(\mathrm{fl}_{p'}(x + y)) = \mathrm{fl}_p(x + y)$. -/
theorem fl_fl_add (hp : 1 ≤ p) {p' : ℕ} (hp' : 2 * p + 1 ≤ p') {x y : K} (hx : IsFloat p x)
    (hy : IsFloat p y) : fl p (fl p' (x + y)) = fl p (x + y) := by
  obtain ⟨d, rfl⟩ : ∃ d, p' = p + d := ⟨p' - p, by omega⟩
  obtain ⟨mx, ex, hmx, rfl⟩ := hx
  obtain ⟨my, ey, hmy, rfl⟩ := hy
  rcases le_total ey ex with h | h
  · exact fl_fl_add_aux hp (by omega) hmx hmy h
  · rw [add_comm ((mx : K) * 2 ^ ex)]
    exact fl_fl_add_aux hp (by omega) hmy hmx h

private theorem fl_fl_sub (hp : 1 ≤ p) {p' : ℕ} (hp' : 2 * p + 1 ≤ p') {x y : K} (hx : IsFloat p x)
    (hy : IsFloat p y) : fl p (fl p' (x - y)) = fl p (x - y) := by
  rw [sub_eq_add_neg]
  exact fl_fl_add hp hp' hx hy.neg

/-- **Innocuous double rounding of products.** Let $K$ be a linearly ordered field with a floor
function and let $p \ge 1$ and $p' \ge 2p$ be natural numbers. For all binary floating-point numbers
$x, y \in K$ with $p$-bit significands and unbounded exponent, rounding $xy$ to nearest, ties to
even, first with $p'$ bits and then with $p$ bits gives the same as rounding it directly with $p$
bits: $\mathrm{fl}_p(\mathrm{fl}_{p'}(xy)) = \mathrm{fl}_p(xy)$. -/
theorem fl_fl_mul (hp : 1 ≤ p) {p' : ℕ} (hp' : 2 * p ≤ p') {x y : K} (hx : IsFloat p x)
    (hy : IsFloat p y) : fl p (fl p' (x * y)) = fl p (x * y) := by
  obtain ⟨mx, ex, hmx, rfl⟩ := hx
  obtain ⟨my, ey, hmy, rfl⟩ := hy
  have hfloat : IsFloat p' ((mx : K) * 2 ^ ex * (my * 2 ^ ey)) := by
    refine ⟨mx * my, ex + ey, ?_, by push_cast; rw [zpow_add₀ two_ne_zero]; ring⟩
    rw [abs_mul]
    calc |mx| * |my| < 2 ^ p * 2 ^ p := mul_lt_mul'' hmx hmy (abs_nonneg _) (abs_nonneg _)
      _ = 2 ^ (2 * p) := by ring
      _ ≤ 2 ^ p' := pow_le_pow_right₀ (by norm_num) hp'
  rw [fl_eq_self (by omega) hfloat]

/-- **Innocuous double rounding of quotients.** Let $K$ be a linearly ordered field with a floor
function and let $p \ge 1$ and $p' \ge 2p$ be natural numbers. For all binary floating-point numbers
$x, y \in K$ with $p$-bit significands and unbounded exponent, rounding $x / y$ to nearest, ties to
even, first with $p'$ bits and then with $p$ bits gives the same as rounding it directly with $p$
bits: $\mathrm{fl}_p(\mathrm{fl}_{p'}(x / y)) = \mathrm{fl}_p(x / y)$.

For $y = 0$ both sides are $0$, with the convention $x / 0 = 0$. -/
theorem fl_fl_div (hp : 1 ≤ p) {p' : ℕ} (hp' : 2 * p ≤ p') {x y : K} (hx : IsFloat p x)
    (hy : IsFloat p y) : fl p (fl p' (x / y)) = fl p (x / y) := by
  obtain ⟨d, rfl⟩ : ∃ d, p' = p + d := ⟨p' - p, by omega⟩
  rcases eq_or_ne (x / y) 0 with hz | hz
  · rw [hz, fl_zero, fl_zero]
  obtain ⟨hM₁, -⟩ := scaled_bounds hp hz
  refine fl_fl_eq_of_near hp (by omega) (mid_or_near_of_floor fun hn => ?_)
  have hM : 1 / 2 ^ 1 ≤ |x / y / 2 ^ ulpExp p (x / y)| :=
    le_trans (by norm_num) (le_trans (one_le_pow₀ (by norm_num)) hM₁)
  calc 1 / 2 ^ (d + 1) ≤ (1 : K) / 2 ^ (p + 1) :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
    _ < _ := forall_far_of_div hp le_rfl hx hy hM _ hn

/-- **Innocuous double rounding of square roots.** Let $p \ge 1$ and $p' \ge 2p + 2$ be natural
numbers. For every real binary floating-point number $x$ with a $p$-bit significand and unbounded
exponent, rounding $\sqrt{x}$ to nearest, ties to even, first with $p'$ bits and then with $p$ bits
gives the same as rounding it directly with $p$ bits:
$\mathrm{fl}_p(\mathrm{fl}_{p'}(\sqrt{x})) = \mathrm{fl}_p(\sqrt{x})$.

For $x < 0$ both sides are $0$, with the convention $\sqrt{x} = 0$. -/
theorem fl_fl_sqrt (hp : 1 ≤ p) {p' : ℕ} (hp' : 2 * p + 2 ≤ p') {x : ℝ} (hx : IsFloat p x) :
    fl p (fl p' √x) = fl p √x := by
  obtain ⟨d, rfl⟩ : ∃ d, p' = p + d := ⟨p' - p, by omega⟩
  rcases le_or_gt x 0 with hx0 | hx0
  · rw [Real.sqrt_eq_zero'.2 hx0, fl_zero, fl_zero]
  have hz : 0 < √x := Real.sqrt_pos.2 hx0
  obtain ⟨hM₁, hM₂⟩ := scaled_bounds hp hz.ne'
  rw [abs_of_pos (div_pos hz (two_zpow_pos _))] at hM₁ hM₂
  refine fl_fl_eq_of_near hp (by omega) (mid_or_near_of_floor fun hn => ?_)
  calc 1 / 2 ^ (d + 1) ≤ (1 : ℝ) / 2 ^ (p + 3) :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
    _ < _ := far_of_sqrt hp hx (le_trans (by norm_num) (le_trans (one_le_pow₀ (by norm_num)) hM₁))
        hM₂ hn


/-! ## Gradual underflow -/

private theorem flIn_zero (q : ℤ) : flIn p q (0 : K) = 0 := by
  have : rne (0 : K) = 0 := by exact_mod_cast rne_intCast (K := K) 0
  simp [flIn, this]

omit [IsStrictOrderedRing K] in
private theorem flIn_eq_fl {q : ℤ} {x : K} (h : q ≤ ulpExp p x) : flIn p q x = fl p x := by
  unfold flIn fl
  rw [max_eq_left h]

private theorem flIn_int_mul_zpow {q m e : ℤ} (hm : |m| < 2 ^ p) (he : q ≤ e) :
    flIn p q ((m : K) * 2 ^ e) = m * 2 ^ e := by
  rcases eq_or_ne m 0 with rfl | hm0
  · simp [flIn_zero]
  have hx0 : (m : K) * 2 ^ e ≠ 0 := mul_ne_zero (by exact_mod_cast hm0) (two_zpow_pos e).ne'
  have hu : ulpExp p ((m : K) * 2 ^ e) ≤ e := by
    apply ulpExp_le_of_abs_lt hx0
    rw [abs_mul, abs_of_pos (two_zpow_pos (K := K) e)]
    exact mul_lt_mul_of_pos_right (by rw [← Int.cast_abs]; exact_mod_cast hm) (two_zpow_pos e)
  obtain ⟨E, hE_def⟩ : ∃ E, E = max (ulpExp p ((m : K) * 2 ^ e)) q := ⟨_, rfl⟩
  have hE : E ≤ e := hE_def ▸ max_le hu he
  have hint : (m : K) * 2 ^ e / 2 ^ E = ((m * 2 ^ (e - E).toNat : ℤ) : K) := by
    push_cast
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_sub₀ two_ne_zero]
    field_simp
  unfold flIn
  rw [← hE_def, hint, rne_intCast, ← hint, div_mul_cancel₀ _ (two_zpow_pos _).ne']

private theorem flIn_eq_of_abs_le (hp : 1 ≤ p) {q e : ℤ} {w : K} (hqe : q ≤ e)
    (h₂ : |w| ≤ 2 ^ p * 2 ^ e) (h₁ : 2 ^ (p - 1) * 2 ^ e ≤ |w| ∨ e = q) :
    flIn p q w = rne (w / 2 ^ e) * 2 ^ e := by
  rcases eq_or_ne w 0 with rfl | hw
  · have : rne (0 : K) = 0 := by exact_mod_cast rne_intCast (K := K) 0
    simp [flIn_zero, this]
  by_cases hlo : (2 : K) ^ (p - 1) * 2 ^ e ≤ |w|
  · rw [flIn_eq_fl (hqe.trans (le_ulpExp_of_le_abs hp hlo)), fl_eq_of_le_of_le hp hlo h₂]
  · obtain rfl : e = q := h₁.resolve_left hlo
    push Not at hlo
    have hu : ulpExp p w ≤ e - 1 := by
      apply ulpExp_le_of_abs_lt hw
      rw [zpow_sub_one₀ two_ne_zero,
        show (2 : K) ^ p = 2 * 2 ^ (p - 1) by rw [← pow_succ', Nat.sub_add_cancel hp]]
      calc |w| < 2 ^ (p - 1) * 2 ^ e := hlo
        _ = 2 * 2 ^ (p - 1) * (2 ^ e * 2⁻¹) := by ring
    unfold flIn
    rw [max_eq_right (by omega)]

/- The double-rounding criterion with gradual underflow: when the exponent of the last place of
`z` in the extended format is `d ≥ 1` below that in the target format, and `z` is a midpoint or
within `1/2 - 2^(-d-1)` of a number of the target format at that scale, double rounding of `z` is
innocuous. -/
private theorem flIn_flIn_eq_of_near (hp : 1 ≤ p) {p' : ℕ} {q q' : ℤ} {d : ℕ} (hd : 1 ≤ d) {z : K}
    (he : max (ulpExp p' z) q' = max (ulpExp p z) q - d)
    (h : (∃ k : ℤ, z / 2 ^ max (ulpExp p z) q = k + 1 / 2) ∨
      ∃ k : ℤ, |z / 2 ^ max (ulpExp p z) q - k| < 1 / 2 - 1 / 2 ^ (d + 1)) :
    flIn p q (flIn p' q' z) = flIn p q z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [flIn_zero]
  obtain ⟨e, he_def⟩ : ∃ e, e = max (ulpExp p z) q := ⟨_, rfl⟩
  rw [← he_def] at he h
  have hE : (0 : K) < 2 ^ e := two_zpow_pos e
  have hD : (0 : K) < 2 ^ d := by positivity
  have hfl : flIn p' q' z = (rne (z / 2 ^ e * 2 ^ d) : K) / 2 ^ d * 2 ^ e := by
    unfold flIn
    rw [he]
    have hz' : z / 2 ^ (e - d) = z / 2 ^ e * 2 ^ d := by
      rw [zpow_sub₀ two_ne_zero, zpow_natCast]
      field_simp
    rw [hz', zpow_sub₀ two_ne_zero, zpow_natCast]
    field_simp
  obtain ⟨hM₁, hM₂⟩ := scaled_bounds hp hz
  have hue : ulpExp p z ≤ e := he_def ▸ le_max_left _ _
  have hM₂' : |z / 2 ^ e| < 2 ^ p := by
    rw [abs_div, abs_of_pos hE, div_lt_iff₀ hE]
    rw [abs_div, abs_of_pos (two_zpow_pos (K := K) _), div_lt_iff₀ (two_zpow_pos _)] at hM₂
    calc |z| < 2 ^ p * 2 ^ ulpExp p z := hM₂
      _ ≤ 2 ^ p * 2 ^ e :=
          mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) hue) (by positivity)
  have hr₂ : |rne (z / 2 ^ e * 2 ^ d)| ≤ (2 : ℤ) ^ (p + d) := by
    apply abs_rne_le_of_abs_le
    rw [abs_mul, abs_of_pos hD]
    push_cast
    rw [pow_add]
    exact (mul_lt_mul_of_pos_right hM₂' hD).le
  have hw₂ : |(rne (z / 2 ^ e * 2 ^ d) : K) / 2 ^ d * 2 ^ e| ≤ 2 ^ p * 2 ^ e := by
    rw [abs_mul, abs_div, abs_of_pos hD, abs_of_pos hE]
    gcongr
    rw [div_le_iff₀ hD, ← pow_add, ← Int.cast_abs]
    exact_mod_cast hr₂
  have hw₁ : 2 ^ (p - 1) * 2 ^ e ≤ |(rne (z / 2 ^ e * 2 ^ d) : K) / 2 ^ d * 2 ^ e| ∨ e = q := by
    rcases le_or_gt q (ulpExp p z) with hq | hq
    · left
      have hee : e = ulpExp p z := he_def ▸ max_eq_left hq
      have hr₁ : (2 : ℤ) ^ (p + d - 1) ≤ |rne (z / 2 ^ e * 2 ^ d)| := by
        apply le_abs_rne_of_le_abs (by positivity)
        rw [abs_mul, abs_of_pos hD, hee]
        push_cast
        calc (2 : K) ^ (p + d - 1) = 2 ^ (p - 1) * 2 ^ d := by
              rw [← pow_add]
              congr 1
              omega
          _ ≤ |z / 2 ^ ulpExp p z| * 2 ^ d := by gcongr
      rw [abs_mul, abs_div, abs_of_pos hD, abs_of_pos hE]
      gcongr
      rw [le_div_iff₀ hD, ← pow_add, show p - 1 + d = p + d - 1 by omega, ← Int.cast_abs]
      exact_mod_cast hr₁
    · exact Or.inr (he_def ▸ max_eq_right hq.le)
  rw [hfl, flIn_eq_of_abs_le hp (he_def ▸ le_max_right _ _) hw₂ hw₁,
    mul_div_cancel_right₀ _ hE.ne', rne_rne_mul_two_pow_div hd h]
  unfold flIn
  rw [← he_def]

omit [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K] in
private theorem IsFloatIn.neg {qmin qmax : ℤ} {x : K} (hx : IsFloatIn p qmin qmax x) :
    IsFloatIn p qmin qmax (-x) := by
  obtain ⟨m, e, hm, h₁, h₂, rfl⟩ := hx
  exact ⟨-m, e, by rwa [abs_neg], h₁, h₂, by push_cast; ring⟩

private theorem flIn_flIn_add_aux (hp : 1 ≤ p) {d : ℕ} (hd : p + 1 ≤ d) {q q' : ℤ} (hq : q' ≤ q)
    {mx my ex ey : ℤ} (hmx : |mx| < 2 ^ p) (hmy : |my| < 2 ^ p) (hle : ey ≤ ex) (hqy : q ≤ ey) :
    flIn p q (flIn (p + d) q' ((mx : K) * 2 ^ ex + my * 2 ^ ey)) =
      flIn p q ((mx : K) * 2 ^ ex + my * 2 ^ ey) := by
  set z : K := mx * 2 ^ ex + my * 2 ^ ey with hz_def
  rcases eq_or_ne z 0 with hz | hz
  · rw [hz, flIn_zero, flIn_zero]
  have hu' : ulpExp (p + d) z = ulpExp p z - d := by
    unfold ulpExp
    push_cast
    ring
  by_cases hex : max (ulpExp (p + d) z) q' ≤ ey
  · -- the sum is a number of the extended format
    obtain ⟨k, hk⟩ := exists_int_mul_of_add (K := K) (mx := mx) (my := my) (ex := ex) (ey := ey)
      (by omega) hex
    rw [← hz_def] at hk
    have hkabs : |k| < 2 ^ (p + d) := by
      refine abs_lt_of_eq_int_mul hk ?_
      obtain ⟨-, h₂⟩ := scaled_bounds (p := p + d) (by omega) hz
      rw [abs_div, abs_of_pos (two_zpow_pos (K := K) _), div_lt_iff₀ (two_zpow_pos _)] at h₂
      calc |z| < 2 ^ (p + d) * 2 ^ ulpExp (p + d) z := h₂
        _ ≤ 2 ^ (p + d) * 2 ^ max (ulpExp (p + d) z) q' :=
            mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) (le_max_left _ _))
              (by positivity)
    rw [hk, flIn_int_mul_zpow hkabs (le_max_right _ _)]
  · -- the smaller operand lies below the last place of the extended format
    push Not at hex
    have hmax : max (ulpExp (p + d) z) q' = ulpExp (p + d) z := by
      rcases le_total q' (ulpExp (p + d) z) with h | h
      · exact max_eq_left h
      · rw [max_eq_right h] at hex
        omega
    rw [hmax, hu'] at hex
    have hqu : q ≤ ulpExp p z := by omega
    apply flIn_flIn_eq_of_near hp (by omega) (d := d) (by rw [hmax, hu', max_eq_left hqu])
    rw [max_eq_left hqu]
    exact Or.inr (exists_abs_sub_lt_of_add hp hd hmx hmy hz_def hz (by omega))

/-- **Innocuous double rounding of sums with gradual underflow.** Let $K$ be a linearly ordered
field with a floor function, let $p \ge 1$ and $p' \ge 2p + 1$ be natural numbers, and let $q$,
$q'$ and $q_{\max}$ be integers with $q' \le q$. Write $\mathrm{fl}_{p,q}$ for rounding to
nearest, ties to even, with $p$-bit significands, gradual underflow below the least exponent $q$
and unbounded exponent. For all numbers $x, y \in K$ of the binary format with $p$-bit
significands and last-place exponents in $[q, q_{\max}]$,
$\mathrm{fl}_{p,q}(\mathrm{fl}_{p',q'}(x + y)) = \mathrm{fl}_{p,q}(x + y)$. -/
theorem flIn_flIn_add (hp : 1 ≤ p) {p' : ℕ} (hp' : 2 * p + 1 ≤ p') {q q' qmax : ℤ}
    (hq : q' ≤ q) {x y : K} (hx : IsFloatIn p q qmax x) (hy : IsFloatIn p q qmax y) :
    flIn p q (flIn p' q' (x + y)) = flIn p q (x + y) := by
  obtain ⟨d, rfl⟩ : ∃ d, p' = p + d := ⟨p' - p, by omega⟩
  obtain ⟨mx, ex, hmx, hqx, -, rfl⟩ := hx
  obtain ⟨my, ey, hmy, hqy, -, rfl⟩ := hy
  rcases le_total ey ex with h | h
  · exact flIn_flIn_add_aux hp (by omega) hq hmx hmy h hqy
  · rw [add_comm ((mx : K) * 2 ^ ex)]
    exact flIn_flIn_add_aux hp (by omega) hq hmy hmx h hqx

private theorem flIn_flIn_sub (hp : 1 ≤ p) {p' : ℕ} (hp' : 2 * p + 1 ≤ p') {q q' qmax : ℤ}
    (hq : q' ≤ q) {x y : K} (hx : IsFloatIn p q qmax x) (hy : IsFloatIn p q qmax y) :
    flIn p q (flIn p' q' (x - y)) = flIn p q (x - y) := by
  rw [sub_eq_add_neg]
  exact flIn_flIn_add hp hp' hq hx hy.neg

/-- **Innocuous double rounding of products with gradual underflow.** Let $K$ be a linearly ordered
field with a floor function, let $p$ and $p' \ge 2p$ be natural numbers and let $q$, $q'$ and
$q_{\max}$ be integers with $q' \le 2q$. Write
$\mathrm{fl}_{p,q}(z) = \operatorname{rne}(z / 2^e) \cdot 2^e$ with
$e = \max(\lfloor \log_2 |z| \rfloor - (p - 1), q)$, where $\operatorname{rne}$ rounds to the
nearest integer with ties to the even one; for $p \ge 1$, this is rounding to nearest, ties to
even, with $p$-bit significands, gradual underflow below the least exponent $q$ and unbounded
exponent. For all numbers $x, y \in K$ of the binary format with $p$-bit significands and
last-place exponents in $[q, q_{\max}]$,
$\mathrm{fl}_{p,q}(\mathrm{fl}_{p',q'}(xy)) = \mathrm{fl}_{p,q}(xy)$.

For $p = 0$ the format holds only $0$, so $x = y = 0$ and both sides are $0$. -/
theorem flIn_flIn_mul {p' : ℕ} (hp' : 2 * p ≤ p') {q q' qmax : ℤ}
    (hq : q' ≤ 2 * q) {x y : K} (hx : IsFloatIn p q qmax x) (hy : IsFloatIn p q qmax y) :
    flIn p q (flIn p' q' (x * y)) = flIn p q (x * y) := by
  obtain ⟨mx, ex, hmx, hqx, -, rfl⟩ := hx
  obtain ⟨my, ey, hmy, hqy, -, rfl⟩ := hy
  have habs : |mx * my| < 2 ^ p' := by
    rw [abs_mul]
    calc |mx| * |my| < 2 ^ p * 2 ^ p := mul_lt_mul'' hmx hmy (abs_nonneg _) (abs_nonneg _)
      _ = 2 ^ (2 * p) := by ring
      _ ≤ 2 ^ p' := pow_le_pow_right₀ (by norm_num) hp'
  rw [show (mx : K) * 2 ^ ex * (my * 2 ^ ey) = ((mx * my : ℤ) : K) * 2 ^ (ex + ey) by
      push_cast
      rw [zpow_add₀ two_ne_zero]
      ring,
    flIn_int_mul_zpow habs (by omega)]

/- The gap between the exponents of the last place in the two formats. -/
private theorem exists_gap {u q q' : ℤ} {D : ℕ} {e : ℤ} (he : e = max u q) {c : ℤ}
    (hc : max (u - D) q' ≤ e - c) (hc0 : 0 ≤ c) :
    ∃ d : ℕ, max (u - D) q' = e - d ∧ c ≤ d :=
  ⟨(e - max (u - D) q').toNat, by omega, by omega⟩

/-- **Innocuous double rounding of quotients with gradual underflow.** Let $K$ be a linearly ordered
field with a floor function, let $p \ge 1$ and $p' \ge 2p$ be natural numbers and let $q$, $q'$
and $q_{\max}$ be integers with $q' \le q - p - 2$. Write $\mathrm{fl}_{p,q}$ for rounding to
nearest, ties to even, with $p$-bit significands, gradual underflow below the least exponent $q$
and unbounded exponent. For all numbers $x, y \in K$ of the binary format with $p$-bit
significands and last-place exponents in $[q, q_{\max}]$,
$\mathrm{fl}_{p,q}(\mathrm{fl}_{p',q'}(x / y)) = \mathrm{fl}_{p,q}(x / y)$.

For $y = 0$ both sides are $0$, with the convention $x / 0 = 0$. -/
theorem flIn_flIn_div (hp : 1 ≤ p) {p' : ℕ} (hp' : 2 * p ≤ p') {q q' qmax : ℤ}
    (hq : q' ≤ q - p - 2) {x y : K} (hx : IsFloatIn p q qmax x) (hy : IsFloatIn p q qmax y) :
    flIn p q (flIn p' q' (x / y)) = flIn p q (x / y) := by
  obtain ⟨D, rfl⟩ : ∃ D, p' = p + D := ⟨p' - p, by omega⟩
  rcases eq_or_ne (x / y) 0 with hz | hz
  · rw [hz, flIn_zero, flIn_zero]
  have hu' : ulpExp (p + D) (x / y) = ulpExp p (x / y) - D := by
    unfold ulpExp
    push_cast
    ring
  obtain ⟨hM₁, hM₂⟩ := scaled_bounds hp hz
  rcases le_or_gt q (ulpExp p (x / y)) with hqu | hqu
  · -- the quotient is in the normal range of the target format
    obtain ⟨d, hd, hpd⟩ := exists_gap (D := D) (q' := q') (rfl : max (ulpExp p (x / y)) q = _)
      (c := p) (by rw [max_eq_left hqu]; exact max_le (by omega) (by omega)) (by omega)
    rw [← hu'] at hd
    apply flIn_flIn_eq_of_near hp (by omega) hd
    rw [max_eq_left hqu]
    refine mid_or_near_of_floor fun hn => ?_
    have hM : 1 / 2 ^ 1 ≤ |x / y / 2 ^ ulpExp p (x / y)| :=
      le_trans (by norm_num) (le_trans (one_le_pow₀ (by norm_num)) hM₁)
    calc 1 / 2 ^ (d + 1) ≤ (1 : K) / 2 ^ (p + 1) :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
      _ < _ := forall_far_of_div hp le_rfl hx.isFloat hy.isFloat hM _ hn
  · -- the quotient is subnormal in the target format
    obtain ⟨d, hd, hpd⟩ := exists_gap (D := D) (q' := q') (rfl : max (ulpExp p (x / y)) q = _)
      (c := p + 1) (by rw [max_eq_right hqu.le]; exact max_le (by omega) (by omega)) (by omega)
    rw [← hu'] at hd
    apply flIn_flIn_eq_of_near hp (by omega) hd
    rw [max_eq_right hqu.le]
    by_cases hsmall : |x / y / 2 ^ q| < 1 / 2 - 1 / 2 ^ (d + 1)
    · exact Or.inr ⟨0, by simpa using hsmall⟩
    push Not at hsmall
    refine mid_or_near_of_floor fun hn => ?_
    have hd' : (1 : K) / 2 ^ (d + 1) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (2 : K) ^ 2 ≤ 2 ^ (d + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have hM : 1 / 2 ^ 2 ≤ |x / y / 2 ^ q| := by linarith
    calc 1 / 2 ^ (d + 1) ≤ (1 : K) / 2 ^ (p + 2) :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
      _ < _ := forall_far_of_div hp (by norm_num) hx.isFloat hy.isFloat hM _ hn

/-- **Innocuous double rounding of square roots with gradual underflow.** Let $p \ge 1$ and
$p' \ge 2p + 2$ be natural numbers and let $q$, $q'$ and $q_{\max}$ be integers with
$q' \le q - p - 2$. Write $\mathrm{fl}_{p,q}$ for rounding to nearest, ties to even, with $p$-bit
significands, gradual underflow below the least exponent $q$ and unbounded exponent. For every real
number $x$ of the binary format with $p$-bit significands and last-place exponents in
$[q, q_{\max}]$, $\mathrm{fl}_{p,q}(\mathrm{fl}_{p',q'}(\sqrt{x})) = \mathrm{fl}_{p,q}(\sqrt{x})$.

For $x < 0$ both sides are $0$, with the convention $\sqrt{x} = 0$. -/
theorem flIn_flIn_sqrt (hp : 1 ≤ p) {p' : ℕ} (hp' : 2 * p + 2 ≤ p') {q q' qmax : ℤ}
    (hq : q' ≤ q - p - 2) {x : ℝ} (hx : IsFloatIn p q qmax x) :
    flIn p q (flIn p' q' √x) = flIn p q √x := by
  obtain ⟨D, rfl⟩ : ∃ D, p' = p + D := ⟨p' - p, by omega⟩
  rcases le_or_gt x 0 with hx0 | hx0
  · rw [Real.sqrt_eq_zero'.2 hx0, flIn_zero, flIn_zero]
  have hz : 0 < √x := Real.sqrt_pos.2 hx0
  have hu' : ulpExp (p + D) √x = ulpExp p √x - D := by
    unfold ulpExp
    push_cast
    ring
  obtain ⟨hM₁, hM₂⟩ := scaled_bounds hp hz.ne'
  rw [abs_of_pos (div_pos hz (two_zpow_pos _))] at hM₁ hM₂
  rcases le_or_gt q (ulpExp p √x) with hqu | hqu
  · obtain ⟨d, hd, hpd⟩ := exists_gap (D := D) (q' := q') (rfl : max (ulpExp p √x) q = _)
      (c := p + 2) (by rw [max_eq_left hqu]; exact max_le (by omega) (by omega)) (by omega)
    rw [← hu'] at hd
    apply flIn_flIn_eq_of_near hp (by omega) hd
    rw [max_eq_left hqu]
    refine mid_or_near_of_floor fun hn => ?_
    calc 1 / 2 ^ (d + 1) ≤ (1 : ℝ) / 2 ^ (p + 3) :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
      _ < _ := far_of_sqrt hp hx.isFloat
          (le_trans (by norm_num) (le_trans (one_le_pow₀ (by norm_num)) hM₁)) hM₂ hn
  · obtain ⟨d, hd, hpd⟩ := exists_gap (D := D) (q' := q') (rfl : max (ulpExp p √x) q = _)
      (c := p + 2) (by rw [max_eq_right hqu.le]; exact max_le (by omega) (by omega)) (by omega)
    rw [← hu'] at hd
    apply flIn_flIn_eq_of_near hp (by omega) hd
    rw [max_eq_right hqu.le]
    have hM0 : 0 < √x / 2 ^ q := div_pos hz (two_zpow_pos _)
    by_cases hsmall : √x / 2 ^ q < 1 / 2 - 1 / 2 ^ (d + 1)
    · exact Or.inr ⟨0, by rw [Int.cast_zero, sub_zero, abs_of_pos hM0]; exact hsmall⟩
    push Not at hsmall
    refine mid_or_near_of_floor fun hn => ?_
    have hd' : (1 : ℝ) / 2 ^ (d + 1) ≤ 1 / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (2 : ℝ) ^ 4 ≤ 2 ^ (d + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have hlt : √x / 2 ^ q < 2 ^ p := by
      rw [div_lt_iff₀ (two_zpow_pos _)]
      rw [div_lt_iff₀ (two_zpow_pos _)] at hM₂
      calc √x < 2 ^ p * 2 ^ ulpExp p √x := hM₂
        _ ≤ 2 ^ p * 2 ^ q :=
            mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) hqu.le) (by positivity)
    calc 1 / 2 ^ (d + 1) ≤ (1 : ℝ) / 2 ^ (p + 3) :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
      _ < _ := far_of_sqrt hp hx.isFloat (by linarith) hlt hn

/-- **Binary32 arithmetic evaluated in binary64.** Write $\mathrm{fl}_{p,q}$ for rounding to
nearest, ties to even, with $p$-bit significands, gradual underflow below the least exponent $q$
and unbounded exponent, so that $\mathrm{fl}_{24,-149}$ and $\mathrm{fl}_{53,-1074}$ are the
roundings of IEEE 754 binary32 and binary64 below overflow. For all real binary32 numbers $x$ and
$y$ (the numbers $m \cdot 2^e$ with $|m| < 2^{24}$ and $-149 \le e \le 104$), rounding the exact
sum, difference, product, quotient or square root to binary64 and then to binary32 gives the same
as rounding it directly to binary32: for $\circ \in \{+, -, \times, /\}$,
$\mathrm{fl}_{24,-149}(\mathrm{fl}_{53,-1074}(x \circ y)) = \mathrm{fl}_{24,-149}(x \circ y)$, and
$\mathrm{fl}_{24,-149}(\mathrm{fl}_{53,-1074}(\sqrt{x})) = \mathrm{fl}_{24,-149}(\sqrt{x})$.

For $y = 0$ and for $x < 0$ both sides of the statements for $x / y$ and $\sqrt{x}$ are $0$, with
the conventions $x / 0 = 0$ and $\sqrt{x} = 0$. Overflow is not modelled. -/
theorem binary32_via_binary64 {x y : ℝ} (hx : IsFloatIn 24 (-149) 104 x)
    (hy : IsFloatIn 24 (-149) 104 y) :
    flIn 24 (-149) (flIn 53 (-1074) (x + y)) = flIn 24 (-149) (x + y) ∧
      flIn 24 (-149) (flIn 53 (-1074) (x - y)) = flIn 24 (-149) (x - y) ∧
      flIn 24 (-149) (flIn 53 (-1074) (x * y)) = flIn 24 (-149) (x * y) ∧
      flIn 24 (-149) (flIn 53 (-1074) (x / y)) = flIn 24 (-149) (x / y) ∧
      flIn 24 (-149) (flIn 53 (-1074) √x) = flIn 24 (-149) √x :=
  ⟨flIn_flIn_add (by norm_num) (by norm_num) (by norm_num) hx hy,
    flIn_flIn_sub (by norm_num) (by norm_num) (by norm_num) hx hy,
    flIn_flIn_mul (by norm_num) (by norm_num) hx hy,
    flIn_flIn_div (by norm_num) (by norm_num) (by norm_num) hx hy,
    flIn_flIn_sqrt (by norm_num) (by norm_num) (by norm_num) hx⟩

private theorem flIn_flIn_sixteen_div_three :
    IsFloatIn 2 0 3 (16 : ℝ) ∧ IsFloatIn 2 0 3 (3 : ℝ) ∧
      flIn 2 0 (flIn 4 0 ((16 : ℝ) / 3)) = 4 ∧ flIn 2 0 ((16 : ℝ) / 3) = 6 := by
  refine ⟨⟨2, 3, by norm_num, by norm_num, le_rfl, by norm_num⟩,
    ⟨3, 0, by norm_num, le_rfl, by norm_num, by norm_num⟩, ?_, ?_⟩
  · have hext : flIn 4 0 ((16 : ℝ) / 3) = 5 := by
      rw [flIn_eq_of_abs_le (e := 0) (by norm_num) le_rfl (by norm_num [abs_of_pos])
        (Or.inr rfl), rne_eq_of_abs_sub_lt (k := 5)]
      · norm_num
      · rw [abs_lt]
        constructor <;> norm_num
    rw [hext, flIn_eq_of_abs_le (e := 1) (by norm_num) (by norm_num) (by norm_num [abs_of_pos])
      (Or.inl (by norm_num [abs_of_pos])),
      show (5 : ℝ) / 2 ^ (1 : ℤ) = ((2 : ℤ) : ℝ) + 1 / 2 by norm_num,
      rne_intCast_add_half_of_even (by decide)]
    norm_num
  · rw [flIn_eq_of_abs_le (e := 1) (by norm_num) (by norm_num) (by norm_num [abs_of_pos])
      (Or.inl (by norm_num [abs_of_pos])), rne_eq_of_abs_sub_lt (k := 3)]
    · norm_num
    · rw [abs_lt]
      constructor <;> norm_num

/-! ## The x87 example -/

private theorem fl_eq_of_le_of_le_mul (hp : 1 ≤ p) {x : K} (k : ℕ)
    (h₁ : (2 : K) ^ (p - 1) ≤ |x| * 2 ^ k)
    (h₂ : |x| * 2 ^ k ≤ 2 ^ p) : fl p x = rne (x * 2 ^ k) / 2 ^ k := by
  have hk : (0 : K) < 2 ^ k := by positivity
  rw [fl_eq_of_le_of_le hp (e := -(k : ℤ))]
  · rw [zpow_neg, zpow_natCast, div_inv_eq_mul, ← div_eq_mul_inv]
  · rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, div_le_iff₀ hk]
    exact h₁
  · rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hk]
    exact h₂

private theorem fl_eq_of_le_of_le_div (hp : 1 ≤ p) {x : K} (k : ℕ)
    (h₁ : (2 : K) ^ (p - 1) * 2 ^ k ≤ |x|)
    (h₂ : |x| ≤ 2 ^ p * 2 ^ k) : fl p x = rne (x / 2 ^ k) * 2 ^ k := by
  have := fl_eq_of_le_of_le hp (x := x) (e := (k : ℤ)) (by rwa [zpow_natCast])
    (by rwa [zpow_natCast])
  rwa [zpow_natCast] at this

private theorem x87_double_rounding :
    IsFloat 53 (1 : ℝ) ∧ IsFloat 53 ((2 : ℝ) ^ (-53 : ℤ) + 2 ^ (-78 : ℤ)) ∧
      fl 53 (1 + ((2 : ℝ) ^ (-53 : ℤ) + 2 ^ (-78 : ℤ))) = 1 + 2 ^ (-52 : ℤ) ∧
      fl 64 (1 + ((2 : ℝ) ^ (-53 : ℤ) + 2 ^ (-78 : ℤ))) = 1 + 2 ^ (-53 : ℤ) ∧
      fl 53 (fl 64 (1 + ((2 : ℝ) ^ (-53 : ℤ) + 2 ^ (-78 : ℤ)))) = 1 := by
  have h64 : fl 64 (1 + ((2 : ℝ) ^ (-53 : ℤ) + 2 ^ (-78 : ℤ))) = 1 + 2 ^ (-53 : ℤ) := by
    rw [fl_eq_of_le_of_le_mul (by norm_num) 63 (by norm_num [abs_of_pos])
      (by norm_num [abs_of_pos]),
      rne_eq_of_abs_sub_lt (k := 2 ^ 63 + 2 ^ 10)]
    · norm_num
    · rw [abs_lt]
      constructor <;> norm_num
  refine ⟨⟨1, 0, by norm_num, by norm_num⟩, ⟨2 ^ 25 + 1, -78, by norm_num, by norm_num⟩, ?_, h64,
    ?_⟩
  · rw [fl_eq_of_le_of_le_mul (by norm_num) 52 (by norm_num [abs_of_pos])
      (by norm_num [abs_of_pos]),
      rne_eq_of_abs_sub_lt (k := 2 ^ 52 + 1)]
    · norm_num
    · rw [abs_lt]
      constructor <;> norm_num
  · rw [h64, fl_eq_of_le_of_le_mul (by norm_num) 52 (by norm_num [abs_of_pos])
      (by norm_num [abs_of_pos]),
      show (1 + (2 : ℝ) ^ (-53 : ℤ)) * 2 ^ 52 = ((2 ^ 52 : ℤ) : ℝ) + 1 / 2 by norm_num,
      rne_intCast_add_half_of_even (by decide)]
    norm_num

/-! ## Optimality of the bounds -/

private theorem exists_fl_fl_add_ne (hp : 2 ≤ p) :
    ∃ x y : K, IsFloat p x ∧ IsFloat p y ∧ fl p (fl (2 * p) (x + y)) ≠ fl p (x + y) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  set B : K := 2 ^ q with hB_def
  have hB : (1 : K) ≤ B := one_le_pow₀ (by norm_num)
  have hB0 : (0 : K) < B := by positivity
  have h1 : (2 : K) ^ (q + 2 - 1) = 2 * B := by rw [show q + 2 - 1 = q + 1 by omega, pow_succ]; ring
  have h2 : (2 : K) ^ (q + 2) = 4 * B := by rw [pow_add]; norm_num; ring
  have h3 : (2 : K) ^ (2 * (q + 2) - 1) = 8 * B ^ 2 := by
    rw [show 2 * (q + 2) - 1 = 2 * q + 3 by omega, pow_add, pow_mul']; norm_num; ring
  have h4 : (2 : K) ^ (2 * (q + 2)) = 16 * B ^ 2 := by
    rw [show 2 * (q + 2) = 2 * q + 4 by omega, pow_add, pow_mul']; norm_num; ring
  have h6 : (2 : K) ^ (q + 1) = 2 * B := by rw [pow_succ]; ring
  refine ⟨1 + 1 / (2 * B), 1 / (4 * B) - 1 / (16 * B ^ 2), ?_, ?_, ?_⟩
  · refine ⟨2 ^ (q + 1) + 1, -((q + 1 : ℕ) : ℤ), ?_, ?_⟩
    · have : (2 : ℤ) ^ (q + 2) = 2 * 2 ^ (q + 1) := by rw [pow_succ]; ring
      have : (2 : ℤ) ≤ 2 ^ (q + 1) := by
        calc (2 : ℤ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (q + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      rw [abs_of_pos (by positivity)]
      omega
    · rw [zpow_neg, zpow_natCast]
      push_cast
      rw [pow_succ, ← hB_def]
      field_simp
  · refine ⟨2 ^ (q + 2) - 1, -((2 * (q + 2) : ℕ) : ℤ), ?_, ?_⟩
    · have : (1 : ℤ) < 2 ^ (q + 2) := one_lt_pow₀ (by norm_num) (by omega)
      rw [abs_of_pos (by omega)]
      omega
    · rw [zpow_neg, zpow_natCast, h4]
      push_cast
      rw [h2]
      field_simp
      ring
  · have hz₁ : (2 : K) ^ (q + 2 - 1) ≤
        |1 + 1 / (2 * B) + (1 / (4 * B) - 1 / (16 * B ^ 2))| * 2 ^ (q + 2 - 1) := by
      rw [abs_of_pos (by field_simp; nlinarith), h1]
      field_simp
      nlinarith
    have hz₂ : |1 + 1 / (2 * B) + (1 / (4 * B) - 1 / (16 * B ^ 2))| * 2 ^ (q + 2 - 1) ≤
        2 ^ (q + 2) := by
      rw [abs_of_pos (by field_simp; nlinarith), h1, h2]
      field_simp
      nlinarith
    -- direct rounding: down to `1 + 1/(2B)`
    have hdirect : fl (q + 2) (1 + 1 / (2 * B) + (1 / (4 * B) - 1 / (16 * B ^ 2))) =
        (2 * B + 1) / (2 * B) := by
      rw [fl_eq_of_le_of_le_mul (by omega) _ hz₁ hz₂, h1,
        rne_eq_of_abs_sub_lt (k := 2 ^ (q + 1) + 1)]
      · push_cast
        rw [h6]
      · push_cast
        rw [h6]
        rw [show (1 + 1 / (2 * B) + (1 / (4 * B) - 1 / (16 * B ^ 2))) * (2 * B) - (2 * B + 1) =
          1 / 2 - 1 / (8 * B) by field_simp; ring]
        rw [abs_of_pos (by rw [sub_pos, div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith)]
        have : (0 : K) < 1 / (8 * B) := div_pos one_pos (by linarith)
        linarith
    -- rounding to `2p` bits: a tie, broken upwards to the midpoint `1 + 3/(4B)`
    have hext : fl (2 * (q + 2)) (1 + 1 / (2 * B) + (1 / (4 * B) - 1 / (16 * B ^ 2))) =
        1 + 3 / (4 * B) := by
      rw [fl_eq_of_le_of_le_mul (by omega) (2 * (q + 2) - 1) ?_ ?_, h3]
      · rw [show (1 + 1 / (2 * B) + (1 / (4 * B) - 1 / (16 * B ^ 2))) * (8 * B ^ 2) =
          ((8 * 2 ^ q * 2 ^ q + 6 * 2 ^ q - 1 : ℤ) : K) + 1 / 2 by
            push_cast; rw [← hB_def]; field_simp; ring,
          rne_intCast_add_half_of_odd ⟨4 * 2 ^ q * 2 ^ q + 3 * 2 ^ q - 1, by ring⟩]
        push_cast
        rw [← hB_def]
        field_simp
        ring
      · rw [h3, abs_of_pos (by field_simp; nlinarith)]
        field_simp
        nlinarith
      · rw [h3, h4, abs_of_pos (by field_simp; nlinarith)]
        field_simp
        nlinarith
    -- and then the tie at `p` bits goes to even, up to `1 + 2/(2B)`
    have hdouble : fl (q + 2) (1 + 3 / (4 * B) : K) = (2 * B + 2) / (2 * B) := by
      rw [fl_eq_of_le_of_le_mul (by omega) (q + 2 - 1) ?_ ?_, h1]
      · rw [show (1 + 3 / (4 * B)) * (2 * B) = ((2 ^ (q + 1) + 1 : ℤ) : K) + 1 / 2 by
            push_cast; rw [h6]; field_simp; ring,
          rne_intCast_add_half_of_odd ⟨2 ^ q, by rw [pow_succ]; ring⟩]
        push_cast
        rw [h6]
        ring
      · rw [h1, abs_of_pos (by positivity)]
        field_simp
        nlinarith
      · rw [h1, h2, abs_of_pos (by positivity)]
        field_simp
        nlinarith
    rw [hext, hdouble, hdirect]
    intro h
    field_simp at h
    linarith

private theorem exists_fl_fl_div_ne (hp : 2 ≤ p) :
    ∃ x y : K, IsFloat p x ∧ IsFloat p y ∧ y ≠ 0 ∧
      fl p (fl (2 * p - 1) (x / y)) ≠ fl p (x / y) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  set B : K := 2 ^ q with hB_def
  have hB : (1 : K) ≤ B := one_le_pow₀ (by norm_num)
  have h1 : (2 : K) ^ (q + 2 - 1) = 2 * B := by rw [show q + 2 - 1 = q + 1 by omega, pow_succ]; ring
  have h2 : (2 : K) ^ (q + 2) = 4 * B := by rw [pow_add]; norm_num; ring
  have h3 : (2 : K) ^ (2 * (q + 2) - 1) = 8 * B ^ 2 := by
    rw [show 2 * (q + 2) - 1 = 2 * q + 3 by omega, pow_add, pow_mul']; norm_num; ring
  have h5 : (2 : K) ^ (2 * (q + 2) - 1 - 1) = 4 * B ^ 2 := by
    rw [show 2 * (q + 2) - 1 - 1 = 2 * q + 2 by omega, pow_add, pow_mul']; norm_num; ring
  have h6 : (2 : K) ^ (q + 1) = 2 * B := by rw [pow_succ]; ring
  have hy0 : (1 : K) - 1 / (4 * B) ≠ 0 := by
    have : 1 / (4 * B) < (1 : K) := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hz : (1 : K) / (1 - 1 / (4 * B)) = 4 * B / (4 * B - 1) := by
    field_simp
  have hz₁ : (1 : K) ≤ 4 * B / (4 * B - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hz₂ : 4 * B / (4 * B - 1) ≤ (2 : K) := by rw [div_le_iff₀ (by linarith)]; linarith
  have h4B : (4 : K) * B - 1 ≠ 0 := (by linarith : (0 : K) < 4 * B - 1).ne'
  refine ⟨1, 1 - 1 / (4 * B),
    ⟨1, 0, by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega), by simp⟩,
    ⟨2 ^ (q + 2) - 1, -((q + 2 : ℕ) : ℤ), ?_, ?_⟩, hy0, ?_⟩
  · have : (1 : ℤ) < 2 ^ (q + 2) := one_lt_pow₀ (by norm_num) (by omega)
    rw [abs_of_pos (by omega)]
    omega
  · rw [zpow_neg, zpow_natCast, h2]
    push_cast
    rw [h2]
    field_simp
  rw [hz]
  have hdirect : fl (q + 2) (4 * B / (4 * B - 1)) = (2 * B + 1) / (2 * B) := by
    rw [fl_eq_of_le_of_le_mul (by omega) (q + 2 - 1) ?_ ?_, h1,
      rne_eq_of_abs_sub_lt (k := 2 ^ (q + 1) + 1)]
    · push_cast
      rw [h6]
    · push_cast
      rw [h6, show 4 * B / (4 * B - 1) * (2 * B) - (2 * B + 1) = -((2 * B - 1) / (4 * B - 1)) by
        field_simp; ring, abs_neg, abs_of_pos (div_pos (by linarith) (by linarith)),
        div_lt_iff₀ (by linarith)]
      linarith
    · rw [h1, abs_of_pos (by linarith)]
      nlinarith
    · rw [h1, h2, abs_of_pos (by linarith)]
      nlinarith
  have hext : fl (2 * (q + 2) - 1) (4 * B / (4 * B - 1)) = 1 + 1 / (4 * B) := by
    rw [fl_eq_of_le_of_le_mul (by omega) (2 * (q + 2) - 1 - 1) ?_ ?_, h5,
      rne_eq_of_abs_sub_lt (k := 4 * 2 ^ q * 2 ^ q + 2 ^ q)]
    · push_cast
      rw [← hB_def]
      field_simp
    · push_cast
      rw [← hB_def, show 4 * B / (4 * B - 1) * (4 * B ^ 2) - (4 * B * B + B) = B / (4 * B - 1) by
        field_simp; ring, abs_of_pos (div_pos (by linarith) (by linarith)),
        div_lt_iff₀ (by linarith)]
      linarith
    · rw [h5, abs_of_pos (by linarith)]
      nlinarith
    · rw [h5, h3, abs_of_pos (by linarith)]
      nlinarith
  have hdouble : fl (q + 2) (1 + 1 / (4 * B) : K) = 1 := by
    rw [fl_eq_of_le_of_le_mul (by omega) (q + 2 - 1) ?_ ?_, h1,
      show (1 + 1 / (4 * B)) * (2 * B) = ((2 ^ (q + 1) : ℤ) : K) + 1 / 2 by
        push_cast; rw [h6]; field_simp; ring,
      rne_intCast_add_half_of_even ⟨2 ^ q, by rw [pow_succ]; ring⟩]
    · push_cast
      rw [h6]
      field_simp
    · rw [h1, abs_of_pos (by positivity)]
      field_simp
      nlinarith
    · rw [h1, h2, abs_of_pos (by positivity)]
      field_simp
      nlinarith
  rw [hext, hdouble, hdirect]
  intro h
  field_simp at h
  linarith

private theorem exists_fl_fl_mul_ne (hp : 4 ≤ p) :
    ∃ x y : K, IsFloat p x ∧ IsFloat p y ∧ fl p (fl (2 * p - 1) (x * y)) ≠ fl p (x * y) := by
  rcases hp.eq_or_lt with rfl | hp
  · -- `p = 4`: `13 × 13 = 169`, as in Figueroa's example
    refine ⟨13, 13, ⟨13, 0, by norm_num, by norm_num⟩, ⟨13, 0, by norm_num, by norm_num⟩, ?_⟩
    have hdirect : fl 4 ((13 : K) * 13) = 176 := by
      rw [fl_eq_of_le_of_le_div (by norm_num) 4 (by norm_num [abs_of_pos])
        (by norm_num [abs_of_pos]),
        rne_eq_of_abs_sub_lt (k := 11)]
      · norm_num
      · rw [abs_lt]
        constructor <;> norm_num
    have hext : fl (2 * 4 - 1) ((13 : K) * 13) = 168 := by
      rw [fl_eq_of_le_of_le_div (by norm_num) 1 (by norm_num [abs_of_pos])
        (by norm_num [abs_of_pos]),
        show (13 : K) * 13 / 2 ^ 1 = ((84 : ℤ) : K) + 1 / 2 by norm_num,
        rne_intCast_add_half_of_even (by decide)]
      norm_num
    have hdouble : fl 4 (168 : K) = 160 := by
      rw [fl_eq_of_le_of_le_div (by norm_num) 4 (by norm_num [abs_of_pos])
        (by norm_num [abs_of_pos]),
        show (168 : K) / 2 ^ 4 = ((10 : ℤ) : K) + 1 / 2 by norm_num,
        rne_intCast_add_half_of_even (by decide)]
      norm_num
    rw [hext, hdouble, hdirect]
    norm_num
  -- `p ≥ 5`: `x = y = 3 · 2^(p-2) - 1`
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 5 := ⟨p - 5, by omega⟩
  set b : K := 2 ^ q with hb_def
  have hb : (1 : K) ≤ b := one_le_pow₀ (by norm_num)
  have h1 : (2 : K) ^ (q + 5 - 1) = 16 * b := by
    rw [show q + 5 - 1 = q + 4 by omega, pow_add]; norm_num; ring
  have h2 : (2 : K) ^ (q + 5) = 32 * b := by rw [pow_add]; norm_num; ring
  have h3 : (2 : K) ^ (2 * (q + 5) - 1) = 512 * b ^ 2 := by
    rw [show 2 * (q + 5) - 1 = 2 * q + 9 by omega, pow_add, pow_mul']; norm_num; ring
  have h5 : (2 : K) ^ (2 * (q + 5) - 1 - 1) = 256 * b ^ 2 := by
    rw [show 2 * (q + 5) - 1 - 1 = 2 * q + 8 by omega, pow_add, pow_mul']; norm_num; ring
  have hfloat : IsFloat (q + 5) (24 * b - 1 : K) := by
    refine ⟨3 * 2 ^ (q + 3) - 1, 0, ?_, ?_⟩
    · have : (2 : ℤ) ^ (q + 5) = 4 * 2 ^ (q + 3) := by rw [pow_add, pow_add]; ring
      have : (1 : ℤ) ≤ 2 ^ (q + 3) := one_le_pow₀ (by norm_num)
      rw [abs_of_pos (by omega)]
      omega
    · push_cast
      rw [pow_add, ← hb_def]
      norm_num
      ring
  refine ⟨24 * b - 1, 24 * b - 1, hfloat, hfloat, ?_⟩
  have hdirect : fl (q + 5) ((24 * b - 1) * (24 * b - 1) : K) = (18 * b - 1) * (32 * b) := by
    rw [fl_eq_of_le_of_le_div (by omega) (q + 5) ?_ ?_, h2,
      rne_eq_of_abs_sub_lt (k := 18 * 2 ^ q - 1)]
    · push_cast
      rw [← hb_def]
    · push_cast
      rw [← hb_def, show (24 * b - 1) * (24 * b - 1) / (32 * b) - (18 * b - 1) =
          -((16 * b - 1) / (32 * b)) by field_simp; ring, abs_neg,
        abs_of_pos (div_pos (by linarith) (by linarith)), div_lt_iff₀ (by linarith)]
      linarith
    · rw [h1, h2, abs_of_pos (by nlinarith)]
      nlinarith
    · rw [h2, abs_of_pos (by nlinarith)]
      nlinarith
  have hext : fl (2 * (q + 5) - 1) ((24 * b - 1) * (24 * b - 1) : K) =
      (288 * b ^ 2 - 24 * b) * 2 := by
    rw [fl_eq_of_le_of_le_div (by omega) 1 ?_ ?_,
      show (24 * b - 1) * (24 * b - 1) / 2 ^ 1 =
        ((288 * 2 ^ q * 2 ^ q - 24 * 2 ^ q : ℤ) : K) + 1 / 2 by push_cast; rw [← hb_def]; ring,
      rne_intCast_add_half_of_even ⟨144 * 2 ^ q * 2 ^ q - 12 * 2 ^ q, by ring⟩]
    · push_cast
      rw [← hb_def]
      ring
    · rw [h5, abs_of_pos (by nlinarith)]
      nlinarith
    · rw [h3, abs_of_pos (by nlinarith)]
      nlinarith
  have hdouble : fl (q + 5) ((288 * b ^ 2 - 24 * b) * 2 : K) = (18 * b - 2) * (32 * b) := by
    rw [fl_eq_of_le_of_le_div (by omega) (q + 5) ?_ ?_, h2,
      show (288 * b ^ 2 - 24 * b) * 2 / (32 * b) = ((18 * 2 ^ q - 2 : ℤ) : K) + 1 / 2 by
        push_cast; rw [← hb_def]; field_simp; ring,
      rne_intCast_add_half_of_even ⟨9 * 2 ^ q - 1, by ring⟩]
    · push_cast
      rw [← hb_def]
    · rw [h1, h2, abs_of_pos (by nlinarith)]
      nlinarith
    · rw [h2, abs_of_pos (by nlinarith)]
      nlinarith
  rw [hext, hdouble, hdirect]
  intro h
  have : (0 : K) < 32 * b := by linarith
  have := mul_right_cancel₀ this.ne' h
  linarith

private theorem exists_fl_fl_sqrt_ne (hp : 1 ≤ p) :
    ∃ x : ℝ, IsFloat p x ∧ 0 ≤ x ∧ fl p (fl (2 * p + 1) √x) ≠ fl p √x := by
  set P : ℝ := 2 ^ p with hP_def
  have hP : (2 : ℝ) ≤ P := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hp
  have hP1 : (2 : ℝ) ^ (p - 1) = P / 2 := by
    rw [hP_def, show p = (p - 1) + 1 from (Nat.sub_add_cancel hp).symm, pow_succ]
    simp
  have hP2 : (2 : ℝ) ^ (2 * p) = P ^ 2 := by rw [pow_mul']
  have hP3 : (2 : ℝ) ^ (2 * p + 1) = 2 * P ^ 2 := by rw [pow_succ, hP2]; ring
  have hx : (0 : ℝ) ≤ 1 - 1 / P := by
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  -- bounds on `√(1 - 1/P)`
  have hz₁ : (P - 1) / P < √(1 - 1 / P) := by
    rw [Real.lt_sqrt (div_nonneg (by linarith) (by linarith))]
    rw [div_pow, div_lt_iff₀ (by positivity)]
    field_simp
    nlinarith
  have hz₂ : √(1 - 1 / P) < (2 * P ^ 2 - P) / (2 * P ^ 2) := by
    rw [Real.sqrt_lt' (div_pos (by nlinarith) (by positivity))]
    rw [div_pow, lt_div_iff₀ (by positivity)]
    field_simp
    nlinarith
  have hz₃ : (2 * P ^ 2 - P - 1 / 2) / (2 * P ^ 2) < √(1 - 1 / P) := by
    rw [Real.lt_sqrt (div_nonneg (by nlinarith) (by positivity))]
    rw [div_pow, div_lt_iff₀ (by positivity)]
    field_simp
    nlinarith
  have hzP : (2 * P ^ 2 - P) / (2 * P ^ 2) = 1 - 1 / (2 * P) := by field_simp
  rw [hzP] at hz₂
  have hz0 : 0 < √(1 - 1 / P) := lt_of_le_of_lt (div_nonneg (by linarith) (by linarith)) hz₁
  refine ⟨1 - 1 / P, ⟨2 ^ p - 1, -(p : ℤ), ?_, ?_⟩, hx, ?_⟩
  · have : (1 : ℤ) < 2 ^ p := one_lt_pow₀ (by norm_num) (by omega)
    rw [abs_of_pos (by omega)]
    omega
  · rw [zpow_neg, zpow_natCast, ← hP_def]
    push_cast
    rw [← hP_def]
    field_simp
  have hdirect : fl p √(1 - 1 / P) = (P - 1) / P := by
    rw [fl_eq_of_le_of_le_mul hp p ?_ ?_, rne_eq_of_abs_sub_lt (k := 2 ^ p - 1)]
    · push_cast
      rw [← hP_def]
    · push_cast
      rw [← hP_def, abs_lt]
      constructor
      · rw [div_lt_iff₀ (by linarith)] at hz₁
        linarith
      · have : √(1 - 1 / P) * P < P - 1 / 2 := by
          calc √(1 - 1 / P) * P < (1 - 1 / (2 * P)) * P :=
                mul_lt_mul_of_pos_right hz₂ (by linarith)
            _ = P - 1 / 2 := by field_simp
        linarith
    · rw [hP1, abs_of_pos hz0, ← hP_def]
      rw [div_lt_iff₀ (by linarith)] at hz₁
      linarith
    · rw [abs_of_pos hz0, ← hP_def]
      have : 1 - 1 / (2 * P) < 1 := by
        have : 0 < 1 / (2 * P) := by positivity
        linarith
      nlinarith
  have hext : fl (2 * p + 1) √(1 - 1 / P) = 1 - 1 / (2 * P) := by
    rw [fl_eq_of_le_of_le_mul (by omega) (2 * p + 1) ?_ ?_, hP3,
      rne_eq_of_abs_sub_lt (k := 2 * 2 ^ p * 2 ^ p - 2 ^ p)]
    · push_cast
      rw [← hP_def]
      field_simp
    · push_cast
      rw [← hP_def, abs_lt]
      constructor
      · rw [div_lt_iff₀ (by positivity)] at hz₃
        nlinarith
      · have : √(1 - 1 / P) * (2 * P ^ 2) < (1 - 1 / (2 * P)) * (2 * P ^ 2) :=
          mul_lt_mul_of_pos_right hz₂ (by positivity)
        have h' : (1 - 1 / (2 * P)) * (2 * P ^ 2) = 2 * P * P - P := by field_simp
        linarith
    · rw [show 2 * p + 1 - 1 = 2 * p by omega, hP2, hP3, abs_of_pos hz0]
      rw [div_lt_iff₀ (by positivity)] at hz₃
      nlinarith
    · rw [hP3, abs_of_pos hz0]
      have : 1 - 1 / (2 * P) < 1 := by
        have : 0 < 1 / (2 * P) := by positivity
        linarith
      nlinarith
  have hu : 0 < 1 - 1 / (2 * P) := by
    have : 1 / (2 * P) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    linarith
  have huP : (1 - 1 / (2 * P)) * P = P - 1 / 2 := by field_simp
  have hdouble : fl p (1 - 1 / (2 * P)) = 1 := by
    have hodd : Odd ((2 : ℤ) ^ p - 1) := by
      refine ⟨2 ^ (p - 1) - 1, ?_⟩
      rw [show (2 : ℤ) ^ p = 2 * 2 ^ (p - 1) by rw [← pow_succ', Nat.sub_add_cancel hp]]
      ring
    rw [fl_eq_of_le_of_le_mul hp p ?_ ?_,
      show (1 - 1 / (2 * P)) * 2 ^ p = (((2 : ℤ) ^ p - 1 : ℤ) : ℝ) + 1 / 2 by
        push_cast; rw [← hP_def, huP]; ring,
      rne_intCast_add_half_of_odd hodd]
    · push_cast
      rw [← hP_def]
      field_simp
      ring
    · rw [hP1, abs_of_pos hu, ← hP_def, huP]
      linarith
    · rw [abs_of_pos hu, ← hP_def, huP]
      linarith
  rw [hext, hdouble, hdirect]
  intro h
  field_simp at h
  linarith

/-! ## Double rounding through an extended precision -/

/-- **Double rounding through an extended precision.** Write $\mathrm{fl}_p$ for rounding to
nearest, ties to even, with $p$-bit significands and unbounded exponent, and call a real number a
$p$-bit floating-point number when it is $m \cdot 2^e$ for integers $m$ and $e$ with $|m| < 2^p$.

1. *The x87 example*, with $p' = 64$ and $p = 53$: the $53$-bit floating-point numbers $1$ and
   $2^{-53} + 2^{-78}$ have a sum that rounds directly to
   $\mathrm{fl}_{53}(1 + 2^{-53} + 2^{-78}) = 1 + 2^{-52}$, but through $64$ bits first to
   $\mathrm{fl}_{64}(1 + 2^{-53} + 2^{-78}) = 1 + 2^{-53}$ and then to
   $\mathrm{fl}_{53}(1 + 2^{-53}) = 1$.
2. *Innocuous double rounding.* For every $p \ge 1$ and all $p$-bit floating-point numbers $x$ and
   $y$: $\mathrm{fl}_p(\mathrm{fl}_{p'}(x \pm y)) = \mathrm{fl}_p(x \pm y)$ if $p' \ge 2p + 1$;
   $\mathrm{fl}_p(\mathrm{fl}_{p'}(xy)) = \mathrm{fl}_p(xy)$ if $p' \ge 2p$;
   $\mathrm{fl}_p(\mathrm{fl}_{p'}(x / y)) = \mathrm{fl}_p(x / y)$ if $p' \ge 2p$ and $y \ne 0$; and
   $\mathrm{fl}_p(\mathrm{fl}_{p'}(\sqrt{x})) = \mathrm{fl}_p(\sqrt{x})$ if $p' \ge 2p + 2$ and
   $x \ge 0$.
3. *The bounds are optimal.* For every $p \ge 2$ there are $p$-bit floating-point numbers $x$, $y$
   with $\mathrm{fl}_p(\mathrm{fl}_{2p}(x + y)) \ne \mathrm{fl}_p(x + y)$, others with
   $\mathrm{fl}_p(\mathrm{fl}_{2p}(x - y)) \ne \mathrm{fl}_p(x - y)$, and others with $y \ne 0$ and
   $\mathrm{fl}_p(\mathrm{fl}_{2p-1}(x / y)) \ne \mathrm{fl}_p(x / y)$; for every $p \ge 4$
   there are such $x$, $y$ with $\mathrm{fl}_p(\mathrm{fl}_{2p-1}(xy)) \ne \mathrm{fl}_p(xy)$; and
   for every $p \ge 1$ there is such an $x \ge 0$ with
   $\mathrm{fl}_p(\mathrm{fl}_{2p+1}(\sqrt{x})) \ne \mathrm{fl}_p(\sqrt{x})$.
4. *Gradual underflow.* Write $\mathrm{fl}_{p,q}$ for rounding to nearest, ties to even, with
   $p$-bit significands, gradual underflow below the least exponent $q$ and unbounded exponent
   (`flIn`). For every $p \ge 1$, all integers $q$, $q'$, $q_{\max}$ and all real numbers $x$, $y$
   of the binary format with $p$-bit significands and last-place exponents in $[q, q_{\max}]$:
   $\mathrm{fl}_{p,q}(\mathrm{fl}_{p',q'}(x \pm y)) = \mathrm{fl}_{p,q}(x \pm y)$ if
   $p' \ge 2p + 1$ and $q' \le q$; the same holds for $xy$ if $p' \ge 2p$ and $q' \le 2q$, for
   $x / y$ if $p' \ge 2p$, $q' \le q - p - 2$ and $y \ne 0$, and for $\sqrt{x}$ if $p' \ge 2p + 2$,
   $q' \le q - p - 2$ and $x \ge 0$.
5. *Some condition on $q'$ is needed.* $16$ and $3$ are numbers of the format with $2$-bit
   significands and last-place exponents in $[0, 3]$, yet
   $\mathrm{fl}_{2,0}(\mathrm{fl}_{4,0}(16 / 3)) = 4$ while $\mathrm{fl}_{2,0}(16 / 3) = 6$,
   although $p' = 4 = 2p$ and $q' = q = 0$.
6. *Binary32 through binary64.* For all real binary32 numbers $x$ and $y$ (the numbers
   $m \cdot 2^e$ with $|m| < 2^{24}$ and $-149 \le e \le 104$),
   $\mathrm{fl}_{24,-149}(\mathrm{fl}_{53,-1074}(x \circ y)) = \mathrm{fl}_{24,-149}(x \circ y)$
   for $\circ \in \{+, -, \times\}$, the same holds for $x / y$ if $y \ne 0$, and
   $\mathrm{fl}_{24,-149}(\mathrm{fl}_{53,-1074}(\sqrt{x})) = \mathrm{fl}_{24,-149}(\sqrt{x})$ if
   $x \ge 0$. -/
theorem innocuous_double_rounding :
    (IsFloat 53 (1 : ℝ) ∧ IsFloat 53 ((2 : ℝ) ^ (-53 : ℤ) + 2 ^ (-78 : ℤ)) ∧
      fl 53 (1 + ((2 : ℝ) ^ (-53 : ℤ) + 2 ^ (-78 : ℤ))) = 1 + 2 ^ (-52 : ℤ) ∧
      fl 64 (1 + ((2 : ℝ) ^ (-53 : ℤ) + 2 ^ (-78 : ℤ))) = 1 + 2 ^ (-53 : ℤ) ∧
      fl 53 (fl 64 (1 + ((2 : ℝ) ^ (-53 : ℤ) + 2 ^ (-78 : ℤ)))) = 1) ∧
    (∀ p p' : ℕ, 1 ≤ p → ∀ x y : ℝ, IsFloat p x → IsFloat p y →
      (2 * p + 1 ≤ p' →
        fl p (fl p' (x + y)) = fl p (x + y) ∧ fl p (fl p' (x - y)) = fl p (x - y)) ∧
      (2 * p ≤ p' → fl p (fl p' (x * y)) = fl p (x * y)) ∧
      (2 * p ≤ p' → y ≠ 0 → fl p (fl p' (x / y)) = fl p (x / y)) ∧
      (2 * p + 2 ≤ p' → 0 ≤ x → fl p (fl p' √x) = fl p √x)) ∧
    (∀ p : ℕ, 2 ≤ p →
      (∃ x y : ℝ, IsFloat p x ∧ IsFloat p y ∧ fl p (fl (2 * p) (x + y)) ≠ fl p (x + y)) ∧
      (∃ x y : ℝ, IsFloat p x ∧ IsFloat p y ∧ fl p (fl (2 * p) (x - y)) ≠ fl p (x - y))) ∧
    (∀ p : ℕ, 4 ≤ p →
      ∃ x y : ℝ, IsFloat p x ∧ IsFloat p y ∧ fl p (fl (2 * p - 1) (x * y)) ≠ fl p (x * y)) ∧
    (∀ p : ℕ, 2 ≤ p →
      ∃ x y : ℝ, IsFloat p x ∧ IsFloat p y ∧ y ≠ 0 ∧
        fl p (fl (2 * p - 1) (x / y)) ≠ fl p (x / y)) ∧
    (∀ p : ℕ, 1 ≤ p →
      ∃ x : ℝ, IsFloat p x ∧ 0 ≤ x ∧ fl p (fl (2 * p + 1) √x) ≠ fl p √x) ∧
    (∀ p p' : ℕ, 1 ≤ p → ∀ q q' qmax : ℤ, ∀ x y : ℝ, IsFloatIn p q qmax x →
      IsFloatIn p q qmax y →
      (2 * p + 1 ≤ p' → q' ≤ q →
        flIn p q (flIn p' q' (x + y)) = flIn p q (x + y) ∧
          flIn p q (flIn p' q' (x - y)) = flIn p q (x - y)) ∧
      (2 * p ≤ p' → q' ≤ 2 * q → flIn p q (flIn p' q' (x * y)) = flIn p q (x * y)) ∧
      (2 * p ≤ p' → q' ≤ q - p - 2 → y ≠ 0 →
        flIn p q (flIn p' q' (x / y)) = flIn p q (x / y)) ∧
      (2 * p + 2 ≤ p' → q' ≤ q - p - 2 → 0 ≤ x →
        flIn p q (flIn p' q' √x) = flIn p q √x)) ∧
    (IsFloatIn 2 0 3 (16 : ℝ) ∧ IsFloatIn 2 0 3 (3 : ℝ) ∧
      flIn 2 0 (flIn 4 0 ((16 : ℝ) / 3)) = 4 ∧ flIn 2 0 ((16 : ℝ) / 3) = 6) ∧
    (∀ x y : ℝ, IsFloatIn 24 (-149) 104 x → IsFloatIn 24 (-149) 104 y →
      flIn 24 (-149) (flIn 53 (-1074) (x + y)) = flIn 24 (-149) (x + y) ∧
      flIn 24 (-149) (flIn 53 (-1074) (x - y)) = flIn 24 (-149) (x - y) ∧
      flIn 24 (-149) (flIn 53 (-1074) (x * y)) = flIn 24 (-149) (x * y) ∧
      (y ≠ 0 → flIn 24 (-149) (flIn 53 (-1074) (x / y)) = flIn 24 (-149) (x / y)) ∧
      (0 ≤ x → flIn 24 (-149) (flIn 53 (-1074) √x) = flIn 24 (-149) √x)) := by
  refine ⟨x87_double_rounding, fun p p' hp x y hx hy => ⟨fun h => ⟨fl_fl_add hp h hx hy,
    fl_fl_sub hp h hx hy⟩, fun h => fl_fl_mul hp h hx hy, fun h _ => fl_fl_div hp h hx hy,
    fun h _ => fl_fl_sqrt hp h hx⟩, fun p hp => ⟨exists_fl_fl_add_ne hp, ?_⟩,
    fun p hp => exists_fl_fl_mul_ne hp, fun p hp => exists_fl_fl_div_ne hp,
    fun p hp => exists_fl_fl_sqrt_ne hp,
    fun p p' hp q q' qmax x y hx hy => ⟨fun h hq => ⟨flIn_flIn_add hp h hq hx hy,
      flIn_flIn_sub hp h hq hx hy⟩, fun h hq => flIn_flIn_mul h hq hx hy,
      fun h hq _ => flIn_flIn_div hp h hq hx hy, fun h hq _ => flIn_flIn_sqrt hp h hq hx⟩,
    flIn_flIn_sixteen_div_three, fun x y hx hy => ?_⟩
  · obtain ⟨x, y, hx, hy, h⟩ := exists_fl_fl_add_ne (K := ℝ) hp
    exact ⟨x, -y, hx, hy.neg, by rwa [sub_neg_eq_add]⟩
  · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := binary32_via_binary64 hx hy
    exact ⟨h₁, h₂, h₃, fun _ => h₄, fun _ => h₅⟩

end Cslib.Algorithms.Lean.FloatingPoint

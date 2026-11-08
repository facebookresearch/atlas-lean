/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.UnitaryDivisor

/-!
# Biunitary divisors

Following Wall, a divisor `d` of `n` is biunitary when `gcd₁(d, n / d) = 1`, where `gcd₁(a, b)`
is the greatest common unitary divisor of `a` and `b` (a unitary divisor of `a` is a divisor `d`
with `gcd(d, a / d) = 1`, `Nat.unitaryDivisors`). This file defines `gcd₁`, the biunitary
divisors, and their sum `σ**(n)`, with the characterization of membership and small values.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall).
-/

namespace MetaMathlibExt

@[expose] public section

/-- The greatest common unitary divisor `gcd₁(a, b)`: the largest number that is a unitary
divisor of both `a` and `b` (`0` when `a = 0` or `b = 0`, which have no unitary divisors).

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
def gcdUnitary (a b : ℕ) : ℕ :=
  (a.unitaryDivisors ∩ b.unitaryDivisors).sup id

/-- `gcd₁` is symmetric.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
theorem gcdUnitary_comm (a b : ℕ) : gcdUnitary a b = gcdUnitary b a := by
  simp [gcdUnitary, Finset.inter_comm]

/-- `gcd₁(0, b) = 0`: `0` has no unitary divisors.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
@[simp]
theorem gcdUnitary_zero_left (b : ℕ) : gcdUnitary 0 b = 0 := by
  simp [gcdUnitary]

/-- `gcd₁(a, 0) = 0`: `0` has no unitary divisors.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
@[simp]
theorem gcdUnitary_zero_right (a : ℕ) : gcdUnitary a 0 = 0 := by
  simp [gcdUnitary]

/-- Every common unitary divisor of `a` and `b` is at most `gcd₁(a, b)`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
theorem le_gcdUnitary {a b d : ℕ} (ha : d ∈ a.unitaryDivisors) (hb : d ∈ b.unitaryDivisors) :
    d ≤ gcdUnitary a b :=
  Finset.le_sup (f := id) (Finset.mem_inter.mpr ⟨ha, hb⟩)

/-- For positive `a` and `b`, `gcd₁(a, b)` is a common unitary divisor of `a` and `b`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
theorem gcdUnitary_mem_unitaryDivisors {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    gcdUnitary a b ∈ a.unitaryDivisors ∧ gcdUnitary a b ∈ b.unitaryDivisors := by
  have hne : (a.unitaryDivisors ∩ b.unitaryDivisors).Nonempty :=
    ⟨1, Finset.mem_inter.mpr ⟨by simp [ha], by simp [hb]⟩⟩
  obtain ⟨d, hd, hsup⟩ := Finset.exists_mem_eq_sup _ hne id
  rw [gcdUnitary, hsup]
  exact Finset.mem_inter.mp hd

/-- For positive `a` and `b`, `gcd₁(a, b)` divides `a`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
theorem gcdUnitary_dvd_left {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : gcdUnitary a b ∣ a :=
  Nat.dvd_of_mem_unitaryDivisors (gcdUnitary_mem_unitaryDivisors ha hb).1

/-- For positive `a` and `b`, `gcd₁(a, b)` divides `b`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
theorem gcdUnitary_dvd_right {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : gcdUnitary a b ∣ b :=
  Nat.dvd_of_mem_unitaryDivisors (gcdUnitary_mem_unitaryDivisors ha hb).2

/-- For positive `a` and `b`, `gcd₁(a, b)` is positive.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
theorem gcdUnitary_pos {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : 0 < gcdUnitary a b :=
  Nat.pos_of_dvd_of_pos (gcdUnitary_dvd_left ha hb) (Nat.pos_of_ne_zero ha)

/-- The biunitary divisors of `n`: the divisors `d` of `n` with `gcd₁(d, n / d) = 1`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
def biunitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun d => gcdUnitary d (n / d) = 1

/-- The sum of the biunitary divisors of `n`, written `σ**(n)`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
def sigmaBiunitary (n : ℕ) : ℕ :=
  ∑ d ∈ biunitaryDivisors n, d

/-- Membership in the biunitary divisors: `d ∣ n`, `n ≠ 0` and `gcd₁(d, n / d) = 1`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
@[simp]
theorem mem_biunitaryDivisors {n d : ℕ} :
    d ∈ biunitaryDivisors n ↔ d ∣ n ∧ n ≠ 0 ∧ gcdUnitary d (n / d) = 1 := by
  simp [biunitaryDivisors, Nat.mem_divisors, and_assoc]

/-- `0` has no biunitary divisors.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
@[simp]
theorem biunitaryDivisors_zero : biunitaryDivisors 0 = ∅ := by
  simp [biunitaryDivisors]

/-- `σ**(0) = 0`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
@[simp]
theorem sigmaBiunitary_zero : sigmaBiunitary 0 = 0 := by
  simp [sigmaBiunitary]

/-- A biunitary divisor of `n` divides `n`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
theorem dvd_of_mem_biunitaryDivisors {n d : ℕ} (h : d ∈ biunitaryDivisors n) : d ∣ n :=
  (mem_biunitaryDivisors.mp h).1

/-- `σ**(1) = 1`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
theorem sigmaBiunitary_one : sigmaBiunitary 1 = 1 := by
  decide

/-- `σ**(4) = 1 + 4 = 5`: the divisor `2` of `4` is not biunitary since `gcd₁(2, 2) = 2`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 3.1 (`σ**(2²) = 5`). -/
theorem sigmaBiunitary_four : sigmaBiunitary 4 = 5 := by
  decide

/-- `σ**(16) = 1 + 2 + 8 + 16 = 27`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, formula (1) at `p = 2`, `e = 4`. -/
theorem sigmaBiunitary_sixteen : sigmaBiunitary 16 = 27 := by
  decide

/-- `σ**(27) = 1 + 3 + 9 + 27 = 40`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 3.6 (`σ**(3³) = 2³ · 5`). -/
theorem sigmaBiunitary_twentySeven : sigmaBiunitary 27 = 40 := by
  decide

/-- `120` is biunitary triperfect: `σ**(120) = 360`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (smallest instances
`120, 672, 2160` with `k = 3`). -/
theorem sigmaBiunitary_oneHundredTwenty : sigmaBiunitary 120 = 3 * 120 := by
  decide

end

end MetaMathlibExt

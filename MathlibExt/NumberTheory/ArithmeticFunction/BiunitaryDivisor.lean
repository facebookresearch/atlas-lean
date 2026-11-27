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

/-- **Greatest common unitary divisor.** For natural numbers $a$ and $b$, $\gcd_1(a, b)$ is the
largest natural number that is a unitary divisor of both $a$ and $b$, where a unitary divisor of
$n$ is a divisor $d$ of $n \neq 0$ with $\gcd(d, n / d) = 1$. If $a = 0$ or $b = 0$, there is no
common unitary divisor and $\gcd_1(a, b) = 0$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
def gcdUnitary (a b : ℕ) : ℕ :=
  (a.unitaryDivisors ∩ b.unitaryDivisors).sup id

/-- **Symmetry of the greatest common unitary divisor.** For all natural numbers $a$ and $b$, the
greatest common unitary divisor satisfies $\gcd_1(a, b) = \gcd_1(b, a)$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
theorem gcdUnitary_comm (a b : ℕ) : gcdUnitary a b = gcdUnitary b a := by
  simp [gcdUnitary, Finset.inter_comm]

/-- **Greatest common unitary divisor with zero on the left.** For every natural number $b$, the
greatest common unitary divisor satisfies $\gcd_1(0, b) = 0$, since $0$ has no unitary divisors.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
@[simp]
theorem gcdUnitary_zero_left (b : ℕ) : gcdUnitary 0 b = 0 := by
  simp [gcdUnitary]

/-- **Greatest common unitary divisor with zero on the right.** For every natural number $a$,
the greatest common unitary divisor satisfies $\gcd_1(a, 0) = 0$, since $0$ has no unitary
divisors.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
@[simp]
theorem gcdUnitary_zero_right (a : ℕ) : gcdUnitary a 0 = 0 := by
  simp [gcdUnitary]

/-- **Common unitary divisors are at most the greatest one.** For natural numbers $a$, $b$ and $d$,
if $d$ is a unitary divisor of both $a$ and $b$, then $d \le \gcd_1(a, b)$, where $\gcd_1(a, b)$ is
the greatest common unitary divisor of $a$ and $b$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
theorem le_gcdUnitary {a b d : ℕ} (ha : d ∈ a.unitaryDivisors) (hb : d ∈ b.unitaryDivisors) :
    d ≤ gcdUnitary a b :=
  Finset.le_sup (f := id) (Finset.mem_inter.mpr ⟨ha, hb⟩)

/-- **The greatest common unitary divisor is a common unitary divisor.** For positive natural
numbers $a$ and $b$, the greatest common unitary divisor $\gcd_1(a, b)$ is a unitary divisor of
$a$ and a unitary divisor of $b$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
theorem gcdUnitary_mem_unitaryDivisors {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    gcdUnitary a b ∈ a.unitaryDivisors ∧ gcdUnitary a b ∈ b.unitaryDivisors := by
  have hne : (a.unitaryDivisors ∩ b.unitaryDivisors).Nonempty :=
    ⟨1, Finset.mem_inter.mpr ⟨by simp [ha], by simp [hb]⟩⟩
  obtain ⟨d, hd, hsup⟩ := Finset.exists_mem_eq_sup _ hne id
  rw [gcdUnitary, hsup]
  exact Finset.mem_inter.mp hd

/-- **The greatest common unitary divisor divides its first argument.** For positive natural
numbers $a$ and $b$, the greatest common unitary divisor $\gcd_1(a, b)$ divides $a$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
theorem gcdUnitary_dvd_left {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : gcdUnitary a b ∣ a :=
  Nat.dvd_of_mem_unitaryDivisors (gcdUnitary_mem_unitaryDivisors ha hb).1

/-- **The greatest common unitary divisor divides its second argument.** For positive natural
numbers $a$ and $b$, the greatest common unitary divisor $\gcd_1(a, b)$ divides $b$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
theorem gcdUnitary_dvd_right {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : gcdUnitary a b ∣ b :=
  Nat.dvd_of_mem_unitaryDivisors (gcdUnitary_mem_unitaryDivisors ha hb).2

/-- **Positivity of the greatest common unitary divisor.** For positive natural numbers $a$ and
$b$, the greatest common unitary divisor $\gcd_1(a, b)$ is positive.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
theorem gcdUnitary_pos {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : 0 < gcdUnitary a b :=
  Nat.pos_of_dvd_of_pos (gcdUnitary_dvd_left ha hb) (Nat.pos_of_ne_zero ha)

/-- **Biunitary divisors.** For a natural number $n$, the biunitary divisors of $n$ are the
divisors $d$ of $n$ with $\gcd_1(d, n/d) = 1$, where $\gcd_1(a, b)$ denotes the greatest common
unitary divisor of $a$ and $b$. For $n = 0$ the set is empty.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
def biunitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun d => gcdUnitary d (n / d) = 1

/-- **Biunitary divisor sum.** For a natural number $n$, $\sigma^{**}(n)$ is the sum of the
biunitary divisors of $n$, that is, of the divisors $d$ of $n$ with $\gcd_1(d, n / d) = 1$, where
$\gcd_1$ denotes the greatest common unitary divisor. Since $0$ has no biunitary divisors,
$\sigma^{**}(0) = 0$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
def sigmaBiunitary (n : ℕ) : ℕ :=
  ∑ d ∈ biunitaryDivisors n, d

/-- **Characterization of biunitary divisors.** For natural numbers $n$ and $d$, $d$ is a biunitary
divisor of $n$ if and only if $d$ divides $n$, $n \neq 0$ and $\gcd_1(d, n / d) = 1$, where
$\gcd_1$ denotes the greatest common unitary divisor.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
@[simp]
theorem mem_biunitaryDivisors {n d : ℕ} :
    d ∈ biunitaryDivisors n ↔ d ∣ n ∧ n ≠ 0 ∧ gcdUnitary d (n / d) = 1 := by
  simp [biunitaryDivisors, Nat.mem_divisors, and_assoc]

/-- **Zero has no biunitary divisors.** The set of biunitary divisors of $0$ is empty.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
@[simp]
theorem biunitaryDivisors_zero : biunitaryDivisors 0 = ∅ := by
  simp [biunitaryDivisors]

/-- **The biunitary divisor sum of $0$.** The sum $\sigma^{**}(0)$ of the biunitary divisors of $0$
equals $0$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
@[simp]
theorem sigmaBiunitary_zero : sigmaBiunitary 0 = 0 := by
  simp [sigmaBiunitary]

/-- **Biunitary divisors divide.** For natural numbers $n$ and $d$, if $d$ is a biunitary
divisor of $n$, then $d$ divides $n$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
theorem dvd_of_mem_biunitaryDivisors {n d : ℕ} (h : d ∈ biunitaryDivisors n) : d ∣ n :=
  (mem_biunitaryDivisors.mp h).1

/-- **The biunitary divisor sum of $1$.** The sum $\sigma^{**}(1)$ of the biunitary divisors of $1$
equals $1$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (after Wall). -/
theorem sigmaBiunitary_one : sigmaBiunitary 1 = 1 := by
  decide

/-- **The biunitary divisor sum of $4$.** The sum $\sigma^{**}(4)$ of the biunitary divisors of $4$
equals $5$.

The biunitary divisors of $4$ are $1$ and $4$: the divisor $2$ is not biunitary, since the greatest
common unitary divisor of $2$ and $2$ is $2$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 3.1 (`σ**(2²) = 5`). -/
theorem sigmaBiunitary_four : sigmaBiunitary 4 = 5 := by
  decide

/-- **The biunitary divisor sum of $16$.** The sum $\sigma^{**}(16)$ of the biunitary divisors of
$16$ equals $1 + 2 + 8 + 16 = 27$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, formula (1) at `p = 2`, `e = 4`. -/
theorem sigmaBiunitary_sixteen : sigmaBiunitary 16 = 27 := by
  decide

/-- **The biunitary divisor sum of $27$.** The sum $\sigma^{**}(27)$ of the biunitary divisors of
$27$ equals $1 + 3 + 9 + 27 = 40$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 3.6 (`σ**(3³) = 2³ · 5`). -/
theorem sigmaBiunitary_twentySeven : sigmaBiunitary 27 = 40 := by
  decide

/-- **$120$ is biunitary triperfect.** The sum $\sigma^{**}(120)$ of the biunitary divisors of
$120$ equals $3 \cdot 120 = 360$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 1 (smallest instances
`120, 672, 2160` with `k = 3`). -/
theorem sigmaBiunitary_oneHundredTwenty : sigmaBiunitary 120 = 3 * 120 := by
  decide

end

end MetaMathlibExt

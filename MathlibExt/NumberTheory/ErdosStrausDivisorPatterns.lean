/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Divisor criteria for Erdős–Straus triples

For a prime `p`, Kyle Bradford, *Elementary Patterns from the Erdős-Straus Conjecture*, INTEGERS 25
(2025), Article A54, describes the solutions of `4/p = 1/x + 1/y + 1/z` with `x ≤ y ≤ z` and
`p ∤ y` (type I) by their smallest denominator `x` and a divisor `d` of `x²`. This file proves both
directions: `erdosStraus_typeI_of_dvd_sq` (Proposition 1) builds such a solution from `x` and `d`,
and `erdosStraus_typeI_exists_dvd_sq` (Proposition 3) shows that every type I solution arises in
this way, with `d = (4x - p) y - p x`. The proposition numbers were checked against the preprint
arXiv:2403.16047v1, *Elemental Patterns from the Erdős Straus Conjecture*.

That preprint's proof of Proposition 3 takes the bounds on `x` and a parametrization of the
solutions from earlier work. The proof here is self-contained. Equation (1) gives `d z = p x y`,
hence `d ((4x - p) z - p x) = p² x²`; since `p ∤ x` and `p ∤ y`, also `p ∤ d`, so `d ∣ x²`. Write
`x² = d e`. The number `4x - p` is prime to `x` and divides `(4x - p) (x + y) = d (4e + 1)`, so it
divides `4e + 1`. If `2x ≥ p + 2`, then `x ≤ y` gives `d ≥ 4x`, so `4e + 1 ≤ x + 1 < 4x - p`, a
contradiction; hence `x ≤ ⌈p/2⌉`.
-/

namespace MetaMathlibExt

/-- **Type I Erdős–Straus triples from divisors of a square.** Let $p$ be a prime and let $x$ be a
natural number with $\lceil p/4 \rceil \le x \le \lceil p/2 \rceil$. If $d$ is a positive divisor
of $x^2$ with $d \equiv -px \pmod{4x - p}$, then there are natural numbers $y$ and $z$ with
$(4x - p)\,y = px + d$ and $(4x - p)\,d\,z = px(px + d)$ such that $x \le y \le z$ and $p \nmid y$.

Since $4x > p$, these equations say $y = (px + d)/(4x - p)$ and $z = p(x + px^2/d)/(4x - p)$.

Source: Kyle Bradford, *Elementary Patterns from the Erdős-Straus Conjecture*, INTEGERS 25 (2025),
Article A54, Proposition 1 (`integers-2025-A54-prop-1`). -/
public theorem erdosStraus_typeI_of_dvd_sq {p x d : ℕ} (hp : p.Prime)
    (hx₁ : (p + 3) / 4 ≤ x) (hx₂ : x ≤ (p + 1) / 2) (hd₀ : 0 < d) (hd : d ∣ x ^ 2)
    (hmod : (4 * x - p : ℤ) ∣ d + p * x) :
    ∃ y z : ℕ, (4 * x - p : ℤ) * y = p * x + d ∧ (4 * x - p : ℤ) * d * z = p * x * (p * x + d) ∧
      x ≤ y ∧ y ≤ z ∧ ¬ p ∣ y := by
  have hp₂ := hp.two_le
  have hp4x : p ≤ 4 * x := by omega
  have hx : 0 < x := by omega
  have hxp : x < p := by omega
  have hcast : ((4 * x - p : ℕ) : ℤ) = 4 * x - p := by
    simp [Nat.cast_sub hp4x]
  obtain ⟨y, hy⟩ : 4 * x - p ∣ p * x + d := by
    rw [← Int.ofNat_dvd, hcast]
    simpa [add_comm] using hmod
  have hsum : 4 * x * y = p * x + d + p * y := by
    rw [hy, ← Nat.add_mul, Nat.sub_add_cancel hp4x]
  -- Multiplying the equation for y by x shows that d also divides pxy.
  have hprod : p * x ^ 2 + d * x + p * x * y = x ^ 2 * (4 * y) := by
    linear_combination x * hsum.symm
  obtain ⟨z, hz⟩ : d ∣ p * x * y := by
    have hdiv : d ∣ p * x ^ 2 + d * x :=
      Nat.dvd_add (dvd_mul_of_dvd_right hd p) (dvd_mul_right d x)
    apply (Nat.dvd_add_right hdiv).mp
    rw [hprod]
    exact dvd_mul_of_dvd_left hd _
  refine ⟨y, z, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hcast]
    exact_mod_cast hy.symm
  · rw [← hcast]
    exact_mod_cast calc
      (4 * x - p) * d * z = p * x * ((4 * x - p) * y) := by rw [mul_assoc, ← hz]; ac_rfl
      _ = p * x * (p * x + d) := by rw [← hy]
  · by_contra! hlt
    have hx₂' : 2 * x ≤ p + 1 := by omega
    have hy₂ : 2 * y + 1 ≤ p := by omega
    nlinarith only [hsum, Nat.mul_le_mul_right y hx₂', Nat.mul_le_mul_right x hy₂, hlt]
  · apply Nat.le_of_mul_le_mul_left _ hd₀
    rw [← hz]
    apply Nat.mul_le_mul_right
    calc
      d ≤ x ^ 2 := Nat.le_of_dvd (pow_pos hx _) hd
      _ ≤ p * x := by rw [sq]; exact Nat.mul_le_mul_right x hxp.le
  · intro hpy
    have hpd : p ∣ d := (Nat.dvd_add_right (dvd_mul_right p x)).mp
      (hy ▸ dvd_mul_of_dvd_right hpy _)
    exact Nat.not_dvd_of_pos_of_lt hx hxp (hp.dvd_of_dvd_pow (hpd.trans hd))

/-- **Divisor criterion necessary for type I Erdős–Straus solutions.** Let $p$ be a prime and let
$x \le y \le z$ be positive integers with $4/p = 1/x + 1/y + 1/z$ and $p \nmid y$. Then
$\lceil p/4 \rceil \le x \le \lceil p/2 \rceil$, and there is a positive divisor $d$ of $x^2$ with
$d \equiv -px \pmod{4x - p}$, $(4x - p)\,y = px + d$ and $(4x - p)\,d\,z = px(px + d)$.

Since $4x > p$, the last two equations say $y = (px + d)/(4x - p)$ and
$z = p(x + px^2/d)/(4x - p)$.

Source: Kyle Bradford, *Elementary Patterns from the Erdős-Straus Conjecture*, INTEGERS 25 (2025),
Article A54, Proposition 3 (`integers-2025-A54-prop-3`). -/
public theorem erdosStraus_typeI_exists_dvd_sq {p x y z : ℕ} (hp : p.Prime) (hx : 0 < x)
    (hxy : x ≤ y) (hyz : y ≤ z) (h : (4 : ℚ) / p = 1 / x + 1 / y + 1 / z) (hpy : ¬ p ∣ y) :
    (p + 3) / 4 ≤ x ∧ x ≤ (p + 1) / 2 ∧
      ∃ d : ℕ, 0 < d ∧ d ∣ x ^ 2 ∧ (4 * x - p : ℤ) ∣ d + p * x ∧
        (4 * x - p : ℤ) * y = p * x + d ∧ (4 * x - p : ℤ) * d * z = p * x * (p * x + d) := by
  have hy : 0 < y := hx.trans_le hxy
  have hz : 0 < z := hy.trans_le hyz
  -- Clear the denominators of equation (1).
  have key : 4 * x * y * z = p * (y * z + x * z + x * y) := by
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hx0 : (x : ℚ) ≠ 0 := by exact_mod_cast hx.ne'
    have hy0 : (y : ℚ) ≠ 0 := by exact_mod_cast hy.ne'
    have hz0 : (z : ℚ) ≠ 0 := by exact_mod_cast hz.ne'
    field_simp at h
    exact_mod_cast (by linear_combination h : (4 * x * y * z : ℚ) = p * (y * z + x * z + x * y))
  -- Since `x ≤ y ≤ z`, equation (1) gives `p < 4 x ≤ 3 p`.
  have hp4x : p < 4 * x := by
    by_contra! hle
    nlinarith [Nat.mul_le_mul_right (y * z) hle, Nat.mul_pos hx hz, Nat.mul_pos hx hy]
  have hxp : x < p := by
    have : 4 * x * (y * z) ≤ 3 * p * (y * z) := by
      nlinarith [Nat.mul_le_mul_left p (Nat.mul_le_mul_right z hxy),
        Nat.mul_le_mul_left p (Nat.mul_le_mul_right y (hxy.trans hyz))]
    have := Nat.le_of_mul_le_mul_right this (Nat.mul_pos hy hz)
    omega
  have hpx : ¬ p ∣ x := Nat.not_dvd_of_pos_of_lt hx hxp
  -- For `p = 2` the only solution is `(1, 2, 2)`, which has `p ∣ y`.
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain rfl : x = 1 := by omega
    have hy2 : y ≤ 2 := by nlinarith
    interval_cases y <;> omega
  -- The divisor is `d = (4 x - p) y - p x`, so that `d z = p x y`.
  have key' : (4 * x - p : ℤ) * y * z = p * x * (y + z) := by
    have : (4 * x * y * z : ℤ) = p * (y * z + x * z + x * y) := by exact_mod_cast key
    linear_combination this
  have hDz : ((4 * x - p : ℤ) * y - p * x) * z = p * x * y := by linear_combination key'
  have hD0 : 0 < (4 * x - p : ℤ) * y - p * x := by
    have h1 : (0 : ℤ) < p * x * y := by exact_mod_cast Nat.mul_pos (Nat.mul_pos hp.pos hx) hy
    have h2 : (0 : ℤ) < z := by exact_mod_cast hz
    by_contra! hle
    nlinarith
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = (4 * x - p : ℤ) * y - p * x :=
    ⟨_, Int.toNat_of_nonneg hD0.le⟩
  have hdy : (4 * x - p : ℤ) * y = p * x + d := by rw [hd]; ring
  have hdz : (d : ℤ) * z = p * x * y := by rw [hd]; exact hDz
  have hd0 : 0 < d := by rw [← hd] at hD0; exact_mod_cast hD0
  -- `d ((4 x - p) z - p x) = p² x²` and `p ∤ d`, so `d ∣ x²`.
  have hdsq : (d : ℤ) * ((4 * x - p) * z - p * x) = p ^ 2 * x ^ 2 := by
    linear_combination (4 * x - p : ℤ) * hdz + (p * x : ℤ) * hdy
  have hpd : ¬ p ∣ d := by
    intro hpd
    have h4xy : p ∣ 4 * x * y := by
      have h1 : (p : ℤ) ∣ d := Int.natCast_dvd_natCast.mpr hpd
      have h2 : (4 * x * y : ℤ) = d + p * (x + y) := by linear_combination hdy
      have h3 : (p : ℤ) ∣ 4 * x * y := h2 ▸ dvd_add h1 (dvd_mul_right _ _)
      exact_mod_cast h3
    rcases (Nat.Prime.dvd_mul hp).mp h4xy with h4x | h
    · rcases (Nat.Prime.dvd_mul hp).mp h4x with h4 | h
      · exact hp2 <| (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp <|
          hp.dvd_of_dvd_pow (by simpa using h4 : p ∣ 2 ^ 2)
      · exact hpx h
    · exact hpy h
  have hdx : d ∣ x ^ 2 := by
    have h1 : d ∣ p ^ 2 * x ^ 2 := by
      have : (d : ℤ) ∣ ((p ^ 2 * x ^ 2 : ℕ) : ℤ) := ⟨_, by push_cast; exact hdsq.symm⟩
      exact_mod_cast this
    exact (((hp.coprime_iff_not_dvd.mpr hpd).pow_left 2).symm).dvd_of_dvd_mul_left h1
  -- Writing `x² = d e`, `4 x - p` is prime to `x` and divides `4 e + 1`.
  obtain ⟨e, he⟩ := hdx
  have he' : (x : ℤ) ^ 2 = d * e := by exact_mod_cast he
  have hcop : IsCoprime (4 * x - p : ℤ) (x ^ 2) := by
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr (hp.coprime_iff_not_dvd.mpr hpx)
    exact IsCoprime.pow_right ⟨-a, 4 * a + b, by linear_combination hab⟩
  have hdvd : (4 * x - p : ℤ) ∣ 4 * e + 1 :=
    hcop.dvd_of_dvd_mul_left ⟨(x + y) * e, by linear_combination he' - (e : ℤ) * hdy⟩
  have hle : (4 * x - p : ℤ) ≤ 4 * e + 1 := Int.le_of_dvd (by positivity) hdvd
  -- If `2 x ≥ p + 2`, then `x ≤ y` forces `d ≥ 4 x`, hence `4 e ≤ x`, contradicting `hle`.
  have h2x : 2 * x ≤ p + 1 := by
    by_contra! hlt
    have hlt' : (p : ℤ) + 2 ≤ 2 * x := by exact_mod_cast hlt
    have hxy' : (x : ℤ) ≤ y := by exact_mod_cast hxy
    have hx' : (0 : ℤ) < x := by exact_mod_cast hx
    have hpos : (0 : ℤ) ≤ 4 * x - p := by
      have : (p : ℤ) < 4 * x := by exact_mod_cast hp4x
      linarith
    have h1 : (4 * x - p : ℤ) * x ≤ (4 * x - p) * y := mul_le_mul_of_nonneg_left hxy' hpos
    have hd4 : (4 * x : ℤ) ≤ d := by nlinarith [mul_le_mul_of_nonneg_left hlt' hx'.le]
    have he4 : (4 * e : ℤ) ≤ x := by
      nlinarith [mul_le_mul_of_nonneg_right hd4 (by positivity : (0 : ℤ) ≤ e)]
    linarith
  refine ⟨by omega, by omega, d, hd0, ⟨e, he⟩, ⟨y, by rw [hdy]; ring⟩, hdy, ?_⟩
  linear_combination (4 * x - p : ℤ) * hdz + (p * x : ℤ) * hdy

end MetaMathlibExt

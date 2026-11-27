/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LucasLehmer

/-!
# The adjusted order of two for the Lucas–Lehmer test

For the product of the odd squarefree parts of a seed minus and plus two, a vanishing
Legendre symbol forces the Mersenne exponent to share a nontrivial factor with the
adjusted order of two.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Odd squarefree part.** For an integer $N$ and a natural number $k$, $k$ is an odd
squarefree part of $N$, written $N^* = k$, when $k$ is odd and squarefree and $N = 2^a m^2 k$
for some natural number $a$ and some integer $m$.

For positive $N$ such a $k$ is unique: it is the squarefree part of $N$ when that is odd, and
half of it otherwise.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Section 7 (definition of `N^*`). -/
def IsOddSquarefreePart (N : ℤ) (k : ℕ) : Prop :=
  Odd k ∧ Squarefree k ∧ ∃ a : ℕ, ∃ m : ℤ, N = 2 ^ a * m ^ 2 * k

/-- **The odd squarefree part of $360$.** The number $5$ is the odd squarefree part of $360$:
$5$ is odd and squarefree, and $360 = 2^a m^2 \cdot 5$ for some natural number $a$ and some
integer $m$.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Section 7 (example
`10 = sqf(360)`). -/
theorem isOddSquarefreePart_360 : IsOddSquarefreePart 360 5 :=
  ⟨by decide, Nat.prime_five.prime.squarefree, 1, 6, by norm_num⟩

/-- **The order $\Omega(m)$ of $2$, doubled when odd.** For a natural number $m$, let $\omega(m)$
be the multiplicative order of $2$ modulo $m$, taken to be $0$ when no positive power of $2$ is
congruent to $1$ modulo $m$ (that is, when $m$ is even). Then $\Omega(m) = 2\omega(m)$ if
$\omega(m)$ is odd, and $\Omega(m) = \omega(m)$ otherwise.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Section 7 (definitions of `ω(m)` and
`Ω(m)`). -/
noncomputable def mersenneOmega (m : ℕ) : ℕ :=
  if Odd (orderOf (2 : ZMod m)) then 2 * orderOf (2 : ZMod m) else orderOf (2 : ZMod m)

/-- **$\Omega$ for the seed $37$.** We have $\Omega(1365) = 12$, where $\Omega(m)$ is the
multiplicative order of $2$ modulo $m$, doubled when that order is odd. Here $1365 = 35 \cdot 39$
is the product of the odd squarefree parts $35$ of $37 - 2$ and $39$ of $37 + 2$, the parts
$s_1^-$ and $s_1^+$ for the seed $s_1 = 37$.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Section 7 (example `s_1 = 37`). -/
theorem mersenneOmega_1365 : mersenneOmega 1365 = 12 := by
  have h : orderOf (2 : ZMod 1365) = 12 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, fun m hm hm0 => ?_⟩
    interval_cases m <;> decide
  rw [mersenneOmega, h]
  decide

set_option linter.unusedVariables false in
/-- **A zero Legendre symbol forces $\gcd(n, \Omega) > 1$.** Let $s_1 \ge 3$ be an integer, let
$s_1^-$ and $s_1^+$ be the odd squarefree parts of $s_1 - 2$ and $s_1 + 2$, and let
$\Omega = \Omega(s_1^- s_1^+)$. Let $p$ be a prime dividing $s_1^- s_1^+$, let $n$ be a natural
number and let $M_n = 2^n - 1$. If the Legendre symbol $\left(\frac{M_n}{p}\right)$ is $0$, then
$\gcd(n, \Omega) > 1$.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Proposition 12. -/
theorem one_lt_gcd_mersenneOmega_of_legendreSym_eq_zero (s₁ : ℤ) (hs₁ : 3 ≤ s₁)
    (sm sp : ℕ) (hsm : IsOddSquarefreePart (s₁ - 2) sm) (hsp : IsOddSquarefreePart (s₁ + 2) sp)
    (p : ℕ) [Fact p.Prime] (hp : p ∣ sm * sp) (n : ℕ)
    (h : legendreSym p (mersenne n) = 0) :
    1 < Nat.gcd n (mersenneOmega (sm * sp)) := by
  have hn : orderOf (2 : ZMod p) ∣ n := by
    apply orderOf_dvd_of_pow_eq_one
    have hz := (legendreSym.eq_zero_iff p _).mp h
    simpa [mersenne, Nat.cast_sub (Nat.one_le_pow n 2 two_pos), sub_eq_zero] using hz
  have hmap : orderOf (2 : ZMod p) ∣ orderOf (2 : ZMod (sm * sp)) := by
    let f := ZMod.castHom hp (ZMod p)
    rw [← map_ofNat f 2]
    exact orderOf_map_dvd f.toMonoidHom 2
  have hΩ : orderOf (2 : ZMod p) ∣ mersenneOmega (sm * sp) := by
    unfold mersenneOmega
    split
    · exact hmap.trans (dvd_mul_left _ _)
    · exact hmap
  have hodd := hsm.1.mul hsp.1
  have : NeZero (sm * sp) := ⟨hodd.pos.ne'⟩
  have hu : IsUnit (2 : ZMod (sm * sp)) :=
    (ZMod.isUnit_iff_coprime 2 _).mpr hodd.coprime_two_left
  have hpos : 0 < mersenneOmega (sm * sp) := by
    have := hu.isOfFinOrder.orderOf_pos
    unfold mersenneOmega
    split <;> omega
  refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨(Nat.gcd_pos_of_pos_right n hpos).ne', ?_⟩
  intro hg
  have hd := Nat.dvd_gcd hn hΩ
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hd
  simp [← one_add_one_eq_two] at hd

end

end MetaMathlibExt

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Modular inverse switching

The switching criterion characterizes when a Bézout coefficient for `m` modulo `n`
is also an inverse of `t` modulo `n`. The two predicates describe least absolute inverses
and the switching identities along a Euclidean remainder sequence. Least absolute inverses
propagate from each remainder to the preceding one. When the first remainder is odd and the
second is even, both initial inverses are extremal exactly when the second remainder is two.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ModInverseSwitchingWanted

/-- **Least absolute inverse.** For integers $x$ and $a$ and a natural number $n$, $x$ is the
least absolute inverse of $a$ modulo $n$ when $xa \equiv 1 \pmod{n}$ and $-n < 2x \le n$, that is,
when $x$ is an inverse of $a$ modulo $n$ in the half-open interval $-n/2 < x \le n/2$.

For even $n$ the endpoint $n/2$ is included and $-n/2$ is excluded; this is also the choice the
Euclidean recurrence produces. -/
def IsLeastAbsInverse (x a : ℤ) (n : ℕ) : Prop :=
  x * a ≡ 1 [ZMOD (n : ℤ)] ∧ -(n : ℤ) < 2 * x ∧ 2 * x ≤ (n : ℤ)

/-- **Euclidean switching data.** A natural number $N$, a sequence $r_0, r_1, \dots$ of natural
numbers and a sequence $s_0, s_1, \dots$ of integers form Euclidean switching data when
$N \ge 1$; $r_0 > r_1 > \cdots > r_{N+1} = 1$, with $r_0, \dots, r_{N+1}$ all positive; for each
$i = 1, \dots, N$ there is a positive integer $q_i$ with $r_{i-1} = q_i r_i + r_{i+1}$;
$s_{N+1} = 1$; and $s_{i+1} r_{i-1} + s_i r_i = 1$ for each $i = 1, \dots, N$.

These are the remainders $r_i$ of the Euclidean algorithm on $(r_0, r_1)$ and the inverses $s_i$
of $r_i$ modulo $r_{i-1}$ in §3 of Konstantogiannis, "The Euclidean Algorithm as a Sequence of
Modular Inverse Switching Formulas" (Equations (4), (5) and (6)). -/
def IsEuclidSwitchSeq (r : ℕ → ℕ) (s : ℕ → ℤ) (N : ℕ) : Prop :=
  0 < N ∧
    (∀ i : ℕ, i ≤ N + 1 → 0 < r i) ∧
    (∀ i : ℕ, i ≤ N → r (i + 1) < r i) ∧
    r (N + 1) = 1 ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ N → ∃ q : ℕ, 0 < q ∧
      r (i - 1) = q * r i + r (i + 1)) ∧
    s (N + 1) = 1 ∧
    ∀ i : ℕ, 1 ≤ i → i ≤ N →
      s (i + 1) * (r (i - 1) : ℤ) + s i * (r i : ℤ) = 1

set_option linter.unusedVariables false in
/-- **Bézout coefficients are modular inverses.** Let $m$ and $n$ be coprime positive integers,
and let $x$ and $y$ be integers with $xm + yn = 1$. Then $xm \equiv 1 \pmod{n}$ and
$yn \equiv 1 \pmod{m}$; that is, $x$ is an inverse of $m$ modulo $n$ and $y$ is an inverse of
$n$ modulo $m$.

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a
Sequence of Modular Inverse Switching Formulas", Lemma 1. -/
theorem bezout_coeffs_are_inverses
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hcop : Nat.Coprime m n)
    (x y : ℤ) (h : x * (m : ℤ) + y * (n : ℤ) = 1) :
    x * (m : ℤ) ≡ 1 [ZMOD (n : ℤ)] ∧
      y * (n : ℤ) ≡ 1 [ZMOD (m : ℤ)] := by
  simp [← h]

set_option linter.unusedVariables false in
/-- **Modular inverse switching.** Let $m$ and $n$ be positive integers with $\gcd(m, n) = 1$,
and let $t$ be an integer with $\gcd(|t|, n) = 1$. Then $m = kn + t$ for some integer $k$ if
and only if there are integers $x$ and $y$ with $xt \equiv 1 \pmod{n}$, $yn \equiv 1 \pmod{m}$
and $xm + yn = 1$.

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a
Sequence of Modular Inverse Switching Formulas", Lemma 2. -/
theorem exists_eq_mul_add_iff_switching
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (t : ℤ)
    (hmn : Nat.Coprime m n) (htn : Nat.Coprime t.natAbs n) :
    (∃ k : ℤ, (m : ℤ) = k * (n : ℤ) + t) ↔
      ∃ x y : ℤ, x * t ≡ 1 [ZMOD (n : ℤ)] ∧
        y * (n : ℤ) ≡ 1 [ZMOD (m : ℤ)] ∧
        x * (m : ℤ) + y * (n : ℤ) = 1 := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨x, y, hxy⟩ := hmn.isCoprime
    have htm : t ≡ (m : ℤ) [ZMOD (n : ℤ)] := by simp [hk]
    exact ⟨x, y, (htm.mul_left x).trans (by simp [← hxy]), by simp [← hxy], hxy⟩
  · rintro ⟨x, y, hxt, _, hxy⟩
    have hxm : x * (m : ℤ) ≡ 1 [ZMOD (n : ℤ)] := by simp [← hxy]
    have htm : t ≡ (m : ℤ) [ZMOD (n : ℤ)] := calc
      t ≡ x * (m : ℤ) * t [ZMOD (n : ℤ)] := by simpa using hxm.symm.mul_right t
      _ = x * t * (m : ℤ) := mul_right_comm _ _ _
      _ ≡ (m : ℤ) [ZMOD (n : ℤ)] := by simpa using hxt.mul_right (m : ℤ)
    simpa only [Int.modEq_iff_add_fac, add_comm t, mul_comm (n : ℤ)] using htm

-- The strict lower bound on x gives one unit of slack because x and n are integers.
private theorem isLeastAbsInverse_succ_imp.switchingBounds {m n x y : ℤ}
    (hm : 2 ≤ m) (hn : 0 < n) (hswitch : x * m + y * n = 1)
    (hlo : -n < 2 * x) (hhi : 2 * x ≤ n) :
    -m < 2 * y ∧ 2 * y ≤ m := by
  have hm₀ : 0 ≤ m := by omega
  have hgap : 1 - n ≤ 2 * x := by omega
  constructor
  · apply lt_of_mul_lt_mul_right _ hn.le
    nlinarith only [hswitch, mul_le_mul_of_nonneg_right hhi hm₀]
  · apply le_of_mul_le_mul_right _ hn
    nlinarith only [hswitch, hm, mul_le_mul_of_nonneg_right hgap hm₀]

/-- **Least absolute inverses propagate down the Euclidean sequence.** Let $r_0, r_1, \ldots$ be
natural numbers, $s_0, s_1, \ldots$ integers and $N \ge 1$ such that $(r, s, N)$ is Euclidean
switching data: $r_0 > r_1 > \cdots > r_{N+1} = 1$ are the successive remainders of the Euclidean
algorithm, $s_{N+1} = 1$, and $s_{i+1} r_{i-1} + s_i r_i = 1$ for $1 \le i \le N$. If
$1 \le j \le N$ and $s_{j+1}$ is the least absolute inverse of $r_{j+1}$ modulo $r_j$, then $s_j$
is the least absolute inverse of $r_j$ modulo $r_{j-1}$.

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a
Sequence of Modular Inverse Switching Formulas", Lemma 3. -/
theorem isLeastAbsInverse_succ_imp
    (r : ℕ → ℕ) (s : ℕ → ℤ) (N : ℕ) (hseq : IsEuclidSwitchSeq r s N)
    (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ N)
    (h : IsLeastAbsInverse (s (j + 1)) (r (j + 1) : ℤ) (r j)) :
    IsLeastAbsInverse (s j) (r j : ℤ) (r (j - 1)) := by
  obtain ⟨_, hpos, hdesc, _, _, _, hswitch⟩ := hseq
  have hbez := hswitch j hj1 hj2
  have hn : 0 < r j := hpos j (by omega)
  have hlt := hdesc (j - 1) (by omega)
  rw [Nat.sub_add_cancel hj1] at hlt
  exact ⟨by simp [← hbez],
    isLeastAbsInverse_succ_imp.switchingBounds (by omega) (by exact_mod_cast hn)
      hbez h.2.1 h.2.2⟩

-- Propagate the half-open bounds backwards from the final inverse, which is one.
private theorem switching_bounds {r : ℕ → ℕ} {s : ℕ → ℤ} {N : ℕ}
    (hseq : IsEuclidSwitchSeq r s N) {i : ℕ} (hi : i ≤ N) :
    -(r i : ℤ) < 2 * s (i + 1) ∧ 2 * s (i + 1) ≤ (r i : ℤ) := by
  obtain ⟨_, hpos, hdesc, hlast, _, hs, hbez⟩ := hseq
  induction hi using Nat.decreasingInduction with
  | self =>
    have h := hdesc N le_rfl
    rw [hlast] at h
    rw [hs]
    omega
  | of_succ i hi ih =>
    obtain ⟨hlo, hhi⟩ := ih
    have h := hbez (i + 1) (by omega) hi
    rw [Nat.add_sub_cancel] at h
    have hp := hpos (i + 1) (by omega)
    have hr := hdesc i hi.le
    exact isLeastAbsInverse_succ_imp.switchingBounds (by omega) (by exact_mod_cast hp) h hlo hhi

/-- **First inverses not both extremal, even–odd case.** Let $(r_i)$, $(s_i)$ and $N$ be
Euclidean switching data with $r_0$ even and $r_1$ odd. Then $2|s_1| < r_0$ or
$2|s_2| < r_1 - 1$; that is, $|s_1| < r_0/2$ or $|s_2| < (r_1 - 1)/2$.

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a
Sequence of Modular Inverse Switching Formulas", Lemma 8. -/
theorem abs_lt_of_even_odd
    (r : ℕ → ℕ) (s : ℕ → ℤ) (N : ℕ) (hseq : IsEuclidSwitchSeq r s N)
    (h0 : Even (r 0)) (h1 : Odd (r 1)) :
    2 * |s 1| < (r 0 : ℤ) ∨ 2 * |s 2| < (r 1 : ℤ) - 1 := by
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  have hm : (r 0 : ℤ) = 2 * a := by omega
  have hn : (r 1 : ℤ) = 2 * b + 1 := by omega
  obtain ⟨hlo, hhi⟩ : -(r 1 : ℤ) < 2 * s 2 ∧ 2 * s 2 ≤ (r 1 : ℤ) :=
    switching_bounds hseq (i := 1) hseq.1
  have hs : |s 2| ≤ (b : ℤ) := abs_le.mpr (by constructor <;> omega)
  obtain ⟨hN, hpos, hdesc, _, _, _, hswitch⟩ := hseq
  have hr : r 1 < r 0 := hdesc 0 (Nat.zero_le _)
  have hr' : r 2 < r 1 := hdesc 1 hN
  have hp := hpos 2 (by omega)
  have ha' : 1 < (a : ℤ) := by omega
  have hbez : s 2 * (r 0 : ℤ) + s 1 * (r 1 : ℤ) = 1 := hswitch 1 le_rfl hN
  left
  by_contra! h
  have hlarge : (a : ℤ) ≤ |s 1| := by omega
  -- The two product bounds differ by a, but the switching identity allows a gap of only one.
  have hle : (a : ℤ) * (r 1 : ℤ) ≤ 1 + (b : ℤ) * (r 0 : ℤ) := calc
    _ ≤ |s 1| * (r 1 : ℤ) := mul_le_mul_of_nonneg_right hlarge (Int.natCast_nonneg _)
    _ = |1 - s 2 * (r 0 : ℤ)| := by rw [← eq_sub_of_add_eq' hbez, abs_mul, Int.abs_natCast]
    _ ≤ 1 + |s 2| * (r 0 : ℤ) := by
      simpa [abs_mul, Int.abs_natCast] using abs_sub (1 : ℤ) (s 2 * (r 0 : ℤ))
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_right hs (Int.natCast_nonneg _)) 1
  rw [hm, hn] at hle
  linarith only [ha', hle]

/-- **Both first inverses extremal, odd–even case.** Let $(r_i)$, $(s_i)$ and $N$ be Euclidean
switching data with $r_0$ odd and $r_1$ even. Then $2|s_1| = r_0 - 1$ and $2|s_2| = r_1$ hold
simultaneously if and only if $r_1 = 2$.

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a
Sequence of Modular Inverse Switching Formulas", Lemma 7. -/
theorem abs_eq_halves_iff_eq_two_of_odd_even
    (r : ℕ → ℕ) (s : ℕ → ℤ) (N : ℕ) (hseq : IsEuclidSwitchSeq r s N)
    (h0 : Odd (r 0)) (h1 : Even (r 1)) :
    (2 * |s 1| = (r 0 : ℤ) - 1 ∧ 2 * |s 2| = (r 1 : ℤ)) ↔
      r 1 = 2 := by
  have ⟨hN, _, _, _, _, _, hswitch⟩ := hseq
  have hbez : s 2 * (r 0 : ℤ) + s 1 * (r 1 : ℤ) = 1 := hswitch 1 le_rfl hN
  constructor
  · rintro ⟨_, hs₂⟩
    obtain ⟨k, hk⟩ := h1
    have hr₁ : (r 1 : ℤ) = 2 * k := by omega
    have habs : |s 2| = (k : ℤ) := by omega
    -- Half the second remainder divides both summands of the Bézout identity.
    have hdvd : (k : ℤ) ∣ (1 : ℤ) := by
      have hs : (k : ℤ) ∣ s 2 := habs ▸ abs_dvd_self (s 2)
      rw [← hbez, hr₁]
      exact dvd_add (hs.mul_right _) ((dvd_mul_left (k : ℤ) 2).mul_left _)
    have hk_one : k = 1 := Nat.dvd_one.mp (by exact_mod_cast hdvd)
    omega
  · intro hr
    obtain ⟨hlo, hhi⟩ : -(r 1 : ℤ) < 2 * s 2 ∧ 2 * s 2 ≤ (r 1 : ℤ) :=
      switching_bounds hseq (i := 1) hN
    rw [hr] at hbez hlo hhi
    have hs₂ : s 2 = 1 := by
      by_contra h
      have hz : s 2 = 0 := by omega
      rw [hz, zero_mul, zero_add] at hbez
      omega
    obtain ⟨k, hk⟩ := h0
    have hr₀ : (r 0 : ℤ) = 2 * k + 1 := by omega
    have hs₁ : s 1 = -(k : ℤ) := by
      rw [hs₂, one_mul, hr₀] at hbez
      omega
    simp [hs₁, hs₂, hr₀, hr]

end MathlibExt.NumberTheory.ModInverseSwitchingWanted

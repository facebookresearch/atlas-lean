/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Modular inverse switching

The switching criterion characterizes when a Bézout coefficient for `m` modulo `n`
is also an inverse of `t` modulo `n`. The two predicates describe least absolute inverses
and the switching identities along a Euclidean remainder sequence.
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

end MathlibExt.NumberTheory.ModInverseSwitchingWanted

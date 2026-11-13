/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# (q, r)-Whitney numbers of the first and second kind

Formalizes the q-integer as a finite geometric sum and the two triangular
recurrence arrays from the source. Concept `jis_sem_1510537ed21edced61e4c308`.
Source statement IDs: `jis_b6c9b8526668212b3d271ce0`, `jis_bfbfab3b67f1c02f167938f1`,
`jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`, `jis_dd5f8c454fc5760fb197859b`.
Original definitions via q-boson operators (`qw1`, `qw2`) are represented here by
the proved triangular recurrences (`identity4`, `identity5`) as the executable
definitions. The first-kind recurrence divides by `q ^ n`, so its API explicitly
assumes `q ≠ 0`; this avoids Lean's totalized inverse assigning unintended values
at the singular parameter `q = 0`.
-/

namespace MetaMathlibExt

@[expose] public section

namespace QRWhitney

/-- **Complex q-integers.** For a complex number $q$ and a natural number $n$, the q-integer
$[n]_q$ is the finite geometric sum $[n]_q = \sum_{i=0}^{n-1} q^i$.

Taking the sum rather than $(1 - q^n)/(1 - q)$ as the definition avoids any singularity at
$q = 1$.

Source: concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
def qBrack (q : ℂ) (n : ℕ) : ℂ :=
  Finset.sum (Finset.range n) (fun i => q ^ i)

/-- **(q, r)-Whitney numbers of the first kind.** Let $m, r, q$ be complex numbers with
$q \ne 0$, and for a natural number $j$ let $[j]_q = \sum_{i=0}^{j-1} q^i$ be the q-integer.
The (q, r)-Whitney numbers of the first kind $w(n, k) = w_{m,r,q}(n, k)$, for natural numbers
$n$ and $k$, are defined by $w(0, 0) = 1$, $w(0, k + 1) = 0$ and, for all $n$ and $k$,
$$w(n + 1, 0) = -q^{-n} (m [n]_q + r) \, w(n, 0),$$
$$w(n + 1, k + 1) = q^{-n} \bigl( w(n, k) - (m [n]_q + r) \, w(n, k + 1) \bigr).$$

Source: concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. The source defines these numbers through q-boson operators and
proves this recurrence (`identity4`); here the recurrence is the definition. -/
noncomputable def whitneyFirst (m r q : ℂ) [NeZero q] : ℕ → ℕ → ℂ
  | 0 => fun | 0 => 1 | _ + 1 => 0
  | n + 1 => fun
    | 0 => (q ^ n)⁻¹ * (0 - (m * qBrack q n + r) * whitneyFirst m r q n 0)
    | k + 1 =>
      (q ^ n)⁻¹ *
        (whitneyFirst m r q n k -
          (m * qBrack q n + r) * whitneyFirst m r q n (k + 1))

/-- **(q, r)-Whitney numbers of the second kind.** For complex numbers $m$, $r$, $q$, the
$(q, r)$-Whitney numbers of the second kind $W_{m,r,q}(n, k)$, indexed by natural numbers $n$
and $k$, are defined by $W_{m,r,q}(0, 0) = 1$, $W_{m,r,q}(0, k + 1) = 0$,
$W_{m,r,q}(n + 1, 0) = r \, W_{m,r,q}(n, 0)$ and
$$
W_{m,r,q}(n + 1, k + 1) = q^k \, W_{m,r,q}(n, k) + (m [k + 1]_q + r) \, W_{m,r,q}(n, k + 1),
$$
where $[j]_q = 1 + q + \dots + q^{j-1}$ is the $q$-integer.

Source: concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
def whitneySecond (m r q : ℂ) : ℕ → ℕ → ℂ
  | 0 => fun | 0 => 1 | _ + 1 => 0
  | n + 1 => fun
    | 0 => r * whitneySecond m r q n 0
    | k + 1 =>
      q ^ k * whitneySecond m r q n k +
        (m * qBrack q (k + 1) + r) * whitneySecond m r q n (k + 1)

/-- **Initial value of the first-kind (q, r)-Whitney numbers.** For all complex numbers
$m, r, q$ with $q \ne 0$, the (q, r)-Whitney number of the first kind satisfies
$w_{m,r,q}(0, 0) = 1$.

Source: concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneyFirst_zero_zero (m r q : ℂ) [NeZero q] : whitneyFirst m r q 0 0 = 1 :=
  rfl

/-- **Row zero of the first-kind (q, r)-Whitney numbers.** For all complex numbers $m, r, q$
with $q \ne 0$ and every natural number $k$, the (q, r)-Whitney number of the first kind
satisfies $w_{m,r,q}(0, k + 1) = 0$.

Source: concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneyFirst_zero_succ (m r q : ℂ) [NeZero q] (k : ℕ) :
    whitneyFirst m r q 0 (k + 1) = 0 :=
  rfl

/-- **Column-zero recurrence for first-kind (q, r)-Whitney numbers.** Let $m, r, q$ be complex
numbers with $q \ne 0$, write $[j]_q$ for the q-integer of $j$, and write $w(n, k)$ for the
(q, r)-Whitney number of the first kind $w_{m,r,q}(n, k)$. Then for every natural number $n$,
$$w(n + 1, 0) = q^{-n} \bigl( 0 - (m [n]_q + r) \, w(n, 0) \bigr).$$

This is the general recurrence with $w(n, -1)$ read as $0$.

Source: concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneyFirst_succ_zero (m r q : ℂ) [NeZero q] (n : ℕ) :
    whitneyFirst m r q (n + 1) 0 =
      (q ^ n)⁻¹ * (0 - (m * qBrack q n + r) * whitneyFirst m r q n 0) :=
  rfl

/-- **Triangular recurrence for first-kind (q, r)-Whitney numbers.** Let $m, r, q$ be complex
numbers with $q \ne 0$, write $[j]_q$ for the q-integer of $j$, and write $w(n, k)$ for the
(q, r)-Whitney number of the first kind $w_{m,r,q}(n, k)$. Then for all natural numbers $n$
and $k$,
$$w(n + 1, k + 1) = q^{-n} \bigl( w(n, k) - (m [n]_q + r) \, w(n, k + 1) \bigr).$$

Source: concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneyFirst_succ_succ (m r q : ℂ) [NeZero q] (n k : ℕ) :
    whitneyFirst m r q (n + 1) (k + 1) =
      (q ^ n)⁻¹ *
        (whitneyFirst m r q n k -
          (m * qBrack q n + r) * whitneyFirst m r q n (k + 1)) :=
  rfl

/-- **Initial value of the second-kind (q, r)-Whitney numbers.** For complex numbers $m$, $r$,
$q$, let $W_{m,r,q}(i, j)$, for natural numbers $i$ and $j$, denote the $(q, r)$-Whitney numbers
of the second kind. Then $W_{m,r,q}(0, 0) = 1$.

Source: concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneySecond_zero_zero (m r q : ℂ) : whitneySecond m r q 0 0 = 1 :=
  rfl

/-- **Row zero of the second-kind (q, r)-Whitney numbers vanishes off the diagonal.** For
complex numbers $m$, $r$, $q$, let $W_{m,r,q}(i, j)$, for natural numbers $i$ and $j$, denote
the $(q, r)$-Whitney numbers of the second kind. Then $W_{m,r,q}(0, k + 1) = 0$ for every
natural number $k$.

Source: concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneySecond_zero_succ (m r q : ℂ) (k : ℕ) :
    whitneySecond m r q 0 (k + 1) = 0 :=
  rfl

/-- **Column-zero recurrence for second-kind (q, r)-Whitney numbers.** For complex numbers $m$,
$r$, $q$, let $W_{m,r,q}(i, j)$, for natural numbers $i$ and $j$, denote the $(q, r)$-Whitney
numbers of the second kind. Then for every natural number $n$,
$W_{m,r,q}(n + 1, 0) = r \, W_{m,r,q}(n, 0)$.

Source: concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneySecond_succ_zero (m r q : ℂ) (n : ℕ) :
    whitneySecond m r q (n + 1) 0 = r * whitneySecond m r q n 0 :=
  rfl

/-- **Triangular recurrence for second-kind (q, r)-Whitney numbers.** For all complex numbers
$m$, $r$, $q$ and all natural numbers $n$ and $k$, the $(q, r)$-Whitney numbers of the second kind
$W_{m,r,q}(n, k)$ satisfy
$$
W_{m,r,q}(n + 1, k + 1) = q^k \, W_{m,r,q}(n, k) + (m [k + 1]_q + r) \, W_{m,r,q}(n, k + 1),
$$
where $[j]_q = 1 + q + \dots + q^{j-1}$ is the $q$-integer.

Source: concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneySecond_succ_succ (m r q : ℂ) (n k : ℕ) :
    whitneySecond m r q (n + 1) (k + 1) =
      q ^ k * whitneySecond m r q n k +
        (m * qBrack q (k + 1) + r) * whitneySecond m r q n (k + 1) :=
  rfl

/-- **First-kind (q, r)-Whitney numbers vanish above the diagonal.** For all complex numbers
$m, r, q$ with $q \ne 0$ and all natural numbers $n$ and $k$ with $n < k$, the (q, r)-Whitney
number of the first kind satisfies $w_{m,r,q}(n, k) = 0$.

Source: concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneyFirst_eq_zero_of_lt {m r q : ℂ} [NeZero q] {n k : ℕ} (h : n < k) :
    whitneyFirst m r q n k = 0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => exact absurd h (by omega)
    | succ k => exact whitneyFirst_zero_succ m r q k
  | succ n ih =>
    cases k with
    | zero => exact absurd h (by omega)
    | succ k =>
      have h1 : n < k := Nat.lt_of_succ_lt_succ h
      have h2 : n < k + 1 := Nat.lt_trans h1 (Nat.lt_succ_self k)
      rw [whitneyFirst_succ_succ, ih h1, ih h2, mul_zero, sub_zero, mul_zero]

/-- **Second-kind (q, r)-Whitney numbers vanish above the diagonal.** For all complex numbers
$m, r, q$ and all natural numbers $n$ and $k$ with $n < k$, the (q, r)-Whitney number of the
second kind satisfies $W_{m,r,q}(n, k) = 0$.

Source: concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneySecond_eq_zero_of_lt {m r q : ℂ} {n k : ℕ} (h : n < k) :
    whitneySecond m r q n k = 0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => exact absurd h (by omega)
    | succ k => exact whitneySecond_zero_succ m r q k
  | succ n ih =>
    cases k with
    | zero => exact absurd h (by omega)
    | succ k =>
      have h1 : n < k := Nat.lt_of_succ_lt_succ h
      have h2 : n < k + 1 := Nat.lt_trans h1 (Nat.lt_succ_self k)
      rw [whitneySecond_succ_succ, ih h1, ih h2, mul_zero, mul_zero, add_zero]

/-- **Triangular recurrence for first-kind (q, r)-Whitney numbers, positive column form.** Let
$m, r, q$ be complex numbers with $q \ne 0$, write $[j]_q$ for the q-integer of $j$, and write
$w(n, k)$ for the (q, r)-Whitney number of the first kind $w_{m,r,q}(n, k)$. Then for all
natural numbers $n$ and $k$ with $k \ge 1$,
$$w(n + 1, k) = q^{-n} \bigl( w(n, k - 1) - (m [n]_q + r) \, w(n, k) \bigr).$$

Source: concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneyFirst_succ_eq (m r q : ℂ) [NeZero q] (n k : ℕ) (hk : 1 ≤ k) :
    whitneyFirst m r q (n + 1) k =
      (q ^ n)⁻¹ *
        (whitneyFirst m r q n (k - 1) -
          (m * qBrack q n + r) * whitneyFirst m r q n k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have h : j + 1 - 1 = j := Nat.add_sub_cancel j 1
  rw [h]
  exact whitneyFirst_succ_succ m r q n j

/-- **Triangular recurrence for second-kind (q, r)-Whitney numbers, positive column form.**
Let $m, r, q$ be complex numbers, write $[j]_q$ for the q-integer of $j$, and write $W(n, k)$
for the (q, r)-Whitney number of the second kind $W_{m,r,q}(n, k)$. Then for all natural numbers
$n$ and $k$ with $k \ge 1$,
$$W(n + 1, k) = q^{k - 1} \, W(n, k - 1) + (m [k]_q + r) \, W(n, k).$$

Source: concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneySecond_succ_eq (m r q : ℂ) (n k : ℕ) (hk : 1 ≤ k) :
    whitneySecond m r q (n + 1) k =
      q ^ (k - 1) * whitneySecond m r q n (k - 1) +
        (m * qBrack q k + r) * whitneySecond m r q n k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have h : j + 1 - 1 = j := Nat.add_sub_cancel j 1
  rw [h]
  exact whitneySecond_succ_succ m r q n j

end QRWhitney

end

end MetaMathlibExt

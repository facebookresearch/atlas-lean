/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Further extensions of Sury's identity

Statements from Gregory Dresden and Xiaoya Gao, "Further Extensions
of Sury's Identity", *Journal of Integer Sequences* 29 (2026),
Article 26.3.2
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Dresden/dresden34.html>).

The generic sequences are taken over `ℚ`.  In Theorem 2 the paper
allows a negative offset `k`; the negative terms are the ones obtained
by running the recurrence backward, which uses `c₂ ≠ 0`.  We encode
that extension directly by requiring the recurrence at every integer
index.

For the Fibonacci and Lucas specializations, `j`-step means the
subsequence of terms with indices `j*n`, and offset `k` means indices
`j*n + k`.  Fibonacci values use Mathlib's signed `Int.fib`, cast to
`ℚ`; its negative-index convention is the standard one used in the
paper.  The Lucas extension below uses `L_{-m} = (-1)^m * L_m`.
Signed values are needed for the `n = 0` case of Theorem 3 and for
negative offsets in Theorem 5.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.Fib.Basic
public import Mathlib.Data.Rat.Defs
public import MathlibExt.NumberTheory.LucasSequence

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted

/-- **Fibonacci numbers extended to negative indices.** For an integer $n$, the Fibonacci number
$F_n$ as a rational number, where $F_0 = 0$, $F_1 = 1$, $F_{m+2} = F_{m+1} + F_m$ for natural
numbers $m$, and $F_{-m} = (-1)^{m+1} F_m$ for natural numbers $m$. -/
abbrev fibAtInt (n : ℤ) : ℚ :=
  (Int.fib n : ℚ)

/-- **Lucas numbers at integer indices.** For an integer $n$, the Lucas number $L_n$ as a
rational number, where $L_0 = 2$, $L_1 = 1$, $L_{m+2} = L_{m+1} + L_m$ for natural numbers $m$,
and $L_{-m} = (-1)^m L_m$ for natural numbers $m$. -/
def lucasAtInt (n : ℤ) : ℚ :=
  if 0 ≤ n then
    (MetaMathlibExt.lucasNumber n.toNat : ℚ)
  else
    (-1 : ℚ) ^ ((-n).toNat) *
      (MetaMathlibExt.lucasNumber (-n).toNat : ℚ)

/-- **Sury's identity for a second-order recurrence starting at 1.** Let $c_1, c_2$ be rational
numbers with $c_2 \neq 0$, and let $(A_n)_{n \ge 0}$ be a sequence of rational numbers with
$A_0 = 1$ and $A_{n+2} = c_1 A_{n+1} + c_2 A_n$ for all $n \ge 0$. Put $t = c_1 - A_1$ and
assume $t \neq 0$. Then for every natural number $n$,
$$A_{n+2} - A_1 A_{n+1} = (A_2 - A_1^2) \sum_{i=0}^{n} t^{n-i} A_i.$$

Source: Gregory Dresden and Xiaoya Gao, "Further Extensions of Sury's Identity", Theorem 1. -/
theorem_wanted second_order_recurrence_initial_one_sury_sum
    (A : ℕ → ℚ) (c₁ c₂ : ℚ)
    (hc₂ : c₂ ≠ 0) (hA0 : A 0 = 1)
    (hrec : ∀ n : ℕ, A (n + 2) = c₁ * A (n + 1) + c₂ * A n)
    (ht : c₁ - A 1 ≠ 0) (n : ℕ) :
    A (n + 2) - A 1 * A (n + 1) =
      (A 2 - A 1 ^ 2) *
        ∑ i ∈ Finset.range (n + 1), (c₁ - A 1) ^ (n - i) * A i

/-- **Offset form of Sury's identity for a second-order recurrence.** Let $c_1, c_2$ be rational
numbers with $c_2 \neq 0$, and let $(X_n)_{n \in \mathbb{Z}}$ be a sequence of rational numbers
with $X_{n+2} = c_1 X_{n+1} + c_2 X_n$ for all integers $n$. Let $k$ be an integer with
$X_k \neq 0$ and $X_{k-1} \neq 0$. Then for every natural number $n$,
$$X_0 X_{n+2} - X_1 X_{n+1} = \frac{X_0 X_2 - X_1^2}{X_k}
\sum_{i=0}^{n} \left(\frac{-c_2 X_{k-1}}{X_k}\right)^{n-i} X_{i+k}.$$

The offset $k$ may be negative; requiring the recurrence at every integer index encodes the
paper's backward extension of the sequence, which uses $c_2 \neq 0$.

Source: Gregory Dresden and Xiaoya Gao, "Further Extensions of Sury's Identity", Theorem 2. -/
theorem_wanted second_order_recurrence_offset_sury_sum
    (X : ℤ → ℚ) (c₁ c₂ : ℚ)
    (hc₂ : c₂ ≠ 0)
    (hrec : ∀ n : ℤ, X (n + 2) = c₁ * X (n + 1) + c₂ * X n)
    (k : ℤ) (hXk : X k ≠ 0) (hXk_pred : X (k - 1) ≠ 0)
    (n : ℕ) :
    X 0 * X ((n : ℤ) + 2) - X 1 * X ((n : ℤ) + 1) =
      ((X 0 * X 2 - X 1 ^ 2) / X k) *
        ∑ i ∈ Finset.range (n + 1),
          (-c₂ * X (k - 1) / X k) ^ (n - i) * X ((i : ℤ) + k)

/-- **Step extension of Sury's identity for Fibonacci numbers.** Let $F_n$ and $L_n$ be the
Fibonacci and Lucas numbers at integer indices. For all natural numbers $j \ge 1$ and $n$,
$$L_j^{n+1} F_{j(n-1)} + (-1)^{j(n+1)} F_{2j} = \sum_{i=0}^{n} (-1)^{j(n+i)} L_j^i F_{ji}.$$

When $n = 0$ the index $j(n-1) = -j$ is negative, so $F_{-j} = (-1)^{j+1} F_j$ enters.

Source: Gregory Dresden and Xiaoya Gao, "Further Extensions of Sury's Identity", Theorem 3. -/
theorem_wanted fib_step_sury_sum
    (j n : ℕ) (hj : 1 ≤ j) :
    lucasAtInt (j : ℤ) ^ (n + 1) *
          fibAtInt ((j : ℤ) * ((n : ℤ) - 1)) +
        (-1 : ℚ) ^ (j * (n + 1)) * fibAtInt (2 * (j : ℤ)) =
      ∑ i ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (j * (n + i)) * lucasAtInt (j : ℤ) ^ i *
          fibAtInt ((j : ℤ) * (i : ℤ))

/-- **Step extension of Sury's identity for Lucas numbers.** Let $F_n$ and $L_n$ be the Fibonacci
and Lucas numbers at integer indices. For all natural numbers $j \ge 1$ and $n$, in the rational
numbers,
$$2 \left(\frac{L_j}{2}\right)^{n+1} \frac{F_{jn}}{F_j} + 2 (-1)^{jn} =
\sum_{i=0}^{n} (-1)^{j(n+i)} \left(\frac{L_j}{2}\right)^i L_{ji}.$$

Source: Gregory Dresden and Xiaoya Gao, "Further Extensions of Sury's Identity", Theorem 4. -/
theorem_wanted lucas_step_sury_sum
    (j n : ℕ) (hj : 1 ≤ j) :
    2 * (lucasAtInt (j : ℤ) / 2) ^ (n + 1) *
          (fibAtInt ((j : ℤ) * (n : ℤ)) / fibAtInt (j : ℤ)) +
        2 * (-1 : ℚ) ^ (j * n) =
      ∑ i ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (j * (n + i)) * (lucasAtInt (j : ℤ) / 2) ^ i *
          lucasAtInt ((j : ℤ) * (i : ℤ))

/-- **Offset step extension of Sury's identity, Fibonacci form.** Let $F_n$ be the Fibonacci
numbers at integer indices. For all natural numbers $j$ and $n$ and every integer $k$ with
$0 < |k| < j$,
$$F_{j(n+1)} = \frac{F_j}{F_k} \sum_{i=0}^{n}
\left(\frac{(-1)^{k+1} F_{j-k}}{F_k}\right)^{n-i} F_{ji+k}.$$

Source: Gregory Dresden and Xiaoya Gao, "Further Extensions of Sury's Identity", Theorem 5, formula (53). -/
theorem_wanted fib_step_offset_sury_sum
    (j : ℕ) (k : ℤ) (n : ℕ)
    (hjk : |k| < (j : ℤ)) (hk : k ≠ 0) :
    fibAtInt ((j : ℤ) * ((n : ℤ) + 1)) =
      (fibAtInt (j : ℤ) / fibAtInt k) *
        ∑ i ∈ Finset.range (n + 1),
          ((-1 : ℚ) ^ (k + 1) * fibAtInt ((j : ℤ) - k) / fibAtInt k) ^
              (n - i) *
            fibAtInt ((j : ℤ) * (i : ℤ) + k)

/-- **Offset step extension of Sury's identity, Lucas form.** Let $F_n$ and $L_n$ be the
Fibonacci and Lucas numbers at integer indices. For all natural numbers $j$ and $n$ and every
integer $k$ with $|k| < j$,
$$F_{j(n+1)} = \frac{F_j}{L_k} \sum_{i=0}^{n}
\left(\frac{(-1)^k L_{j-k}}{L_k}\right)^{n-i} L_{ji+k}.$$

Source: Gregory Dresden and Xiaoya Gao, "Further Extensions of Sury's Identity", Theorem 5, formula (54). -/
theorem_wanted lucas_step_offset_sury_fib_sum
    (j : ℕ) (k : ℤ) (n : ℕ)
    (hjk : |k| < (j : ℤ)) :
    fibAtInt ((j : ℤ) * ((n : ℤ) + 1)) =
      (fibAtInt (j : ℤ) / lucasAtInt k) *
        ∑ i ∈ Finset.range (n + 1),
          ((-1 : ℚ) ^ k * lucasAtInt ((j : ℤ) - k) / lucasAtInt k) ^
              (n - i) *
            lucasAtInt ((j : ℤ) * (i : ℤ) + k)

end MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted

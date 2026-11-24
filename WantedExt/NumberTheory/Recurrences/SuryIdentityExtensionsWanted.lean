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

For the Fibonacci and Lucas specializations, `j`-step means the
subsequence of terms with indices `j*n`, and offset `k` means indices
`j*n + k`.  Fibonacci values use Mathlib's signed `Int.fib`, cast to
`ℚ`; its negative-index convention is the standard one used in the
paper.  The Lucas extension uses `L_{-m} = (-1)^m * L_m`.
Signed values are needed for the `n = 0` case of Theorem 3 and for
negative offsets in Theorem 5.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensions

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted

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

/-- **Offset step extension of Sury's identity, Fibonacci form.** Let $F_n$ be the Fibonacci
numbers at integer indices. For all natural numbers $j$ and $n$ and every integer $k$ with
$0 < |k| < j$,
$$F_{j(n+1)} = \frac{F_j}{F_k} \sum_{i=0}^{n}
\left(\frac{(-1)^{k+1} F_{j-k}}{F_k}\right)^{n-i} F_{ji+k}.$$

Source: Gregory Dresden and Xiaoya Gao, "Further Extensions of Sury's Identity", Theorem 5, formula
(53). -/
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

Source: Gregory Dresden and Xiaoya Gao, "Further Extensions of Sury's Identity", Theorem 5, formula
(54). -/
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

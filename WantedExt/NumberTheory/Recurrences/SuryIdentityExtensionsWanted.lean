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
paper.  The Lucas extension uses `L_{-m} = (-1)^m * L_m`.
Signed values are needed for the `n = 0` case of Theorem 3 and for
negative offsets in Theorem 5 (`lucas_step_offset_sury_fib_sum`, now proved in
`MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsLucasStepOffsetSuryFibSum`).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.Recurrences.FibonacciStepSuryIdentity
public import MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensions
public import MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsFibStepOffsetSurySum
public import MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsLucasStepOffsetSuryFibSum

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted

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

end MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted

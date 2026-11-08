/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import WantedExt.NumberTheory.LeonardoPWanted

namespace MetaMathlibExt

@[expose] public section

/-- The generalized Leonardo numbers `L_{k,n}`: `L_{k,0} = L_{k,1} = 1` and
`L_{k,n+2} = L_{k,n+1} + L_{k,n} + k`. The paper fixes `k` positive; the
recurrence here is stated over `ℤ` (an intentional domain extension,
bridged to the existing `p = 1` API by
`genLeonardo_eq_leonardoPK_one` below).

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly 62.3 (2024), introduction. -/
public def genLeonardo (k : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => genLeonardo k (n + 1) + genLeonardo k n + k

/-- Characteristic value `L_{k,2} = 2 + k`.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024). -/
public theorem genLeonardo_two (k : ℤ) : genLeonardo k 2 = 2 + k := rfl

/-- Bridge to the existing generalized Leonardo `p`-number API: on
natural `k`, `genLeonardo` agrees with `leonardoPK 1` from
`WantedExt.NumberTheory.LeonardoPWanted` (initial values `1, 1` and
the same recurrence). The `ℤ`-valued parameter here is the
intentional extension beyond the paper's positive-`k` domain.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*,
Fibonacci Quarterly 62.3 (2024), introduction; Kusrini, Putra, and
Kuhapatanakul, *On Generalized Leonardo p-Numbers*, Journal of
Integer Sequences 27 (2024), Article 24.4.6. -/
public theorem_wanted genLeonardo_eq_leonardoPK_one (k n : ℕ) :
    genLeonardo (k : ℤ) n
      = MathlibExt.NumberTheory.LeonardoPWanted.leonardoPK 1 k n

/-- The dual generalized Leonardo numbers `M_{k,n}`: the paper's
Definition 2.1 gives `M_{k,0} = 1 - k`, `M_{k,1} = k + 3`, and
`M_{k,n+1} = M_{k,n} + M_{k,n-1} + 2k` for `n ≥ 1`; the paper's
identity (2.1) gives `M_{k,n} = L_{k,n-1} + L_{k,n+1}`. The
closed form used here agrees with Definition 2.1 on all `n` and
with the paper's value table (checked for `k = 1` to `n = 14`).

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*,
Fibonacci Quarterly 62.3 (2024), Definition 2.1 and identity (2.1). -/
public def genLeonardoCompanion (k : ℤ) : ℕ → ℤ
  | 0 => 1 - k
  | n + 1 => genLeonardo k n + genLeonardo k (n + 2)

/-- Characteristic value `M_{k,1} = 3 + k`.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024). -/
public theorem genLeonardoCompanion_one (k : ℤ) :
    genLeonardoCompanion k 1 = 3 + k := by
  show genLeonardo k 0 + genLeonardo k 2 = 3 + k
  have h0 : genLeonardo k 0 = 1 := rfl
  rw [h0, genLeonardo_two]
  ring

/-- The product identity `L_{k,n} * M_{k,n} = (k+1) * L_{k,2n+1} -
k * L_{k,n+3} + k * (2k+1)`.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024), Theorem 2.2 (`fq-2024-kuhapatanakul05292024-thm-2.2`). -/
public theorem_wanted genLeonardo_mul_companion (k : ℤ) (n : ℕ) :
    genLeonardo k n * genLeonardoCompanion k n
      = (k + 1) * genLeonardo k (2 * n + 1) - k * genLeonardo k (n + 3)
        + k * (2 * k + 1)

/-- The cross-product identity `L_{k,n} * M_{k,n+1} - L_{k,n+1} * M_{k,n-1}
= (k+1) * L_{k,2n} - k * L_{k,n} + k`.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024), Theorem 2.3 (`fq-2024-kuhapatanakul05292024-thm-2.3`). -/
public theorem_wanted genLeonardo_cross (k : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    genLeonardo k n * genLeonardoCompanion k (n + 1)
        - genLeonardo k (n + 1) * genLeonardoCompanion k (n - 1)
      = (k + 1) * genLeonardo k (2 * n) - k * genLeonardo k n + k

/-- The square-difference identity `M_{k,n}^2 - L_{k,n}^2 =
4 * L_{k,n-1} * L_{k,n+1} + 2k * L_{k,n} + k^2`.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024), Theorem 2.4 (`fq-2024-kuhapatanakul05292024-thm-2.4`). -/
public theorem_wanted genLeonardo_sq_sub_sq (k : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    genLeonardoCompanion k n ^ 2 - genLeonardo k n ^ 2
      = 4 * genLeonardo k (n - 1) * genLeonardo k (n + 1)
        + 2 * k * genLeonardo k n + k ^ 2

/-- The shift identity
`L_{k,m} L_{k,n} - L_{k,m+t} L_{k,n-t}
= (-1)^{n-t+1} (L_{k,m-n+t-1} + k)(L_{k,t-1} + k)
- k (L_{k,m} + L_{k,n} - L_{k,m+t} - L_{k,n-t})`.

Stated here for `1 ≤ t ≤ n` with `n + 1 ≤ m + t` so that all indices are
nonnegative; the paper allows `t = 0` with `L_{k,-1}` read by backward
extension.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024), Theorem 2.5 (`fq-2024-kuhapatanakul05292024-thm-2.5`). -/
public theorem_wanted genLeonardo_shift (k : ℤ) (m n t : ℕ)
    (ht : 1 ≤ t) (htn : t ≤ n) (hmt : n + 1 ≤ m + t) :
    genLeonardo k m * genLeonardo k n
        - genLeonardo k (m + t) * genLeonardo k (n - t)
      = (-1 : ℤ) ^ (n - t + 1)
          * (genLeonardo k (m + t - n - 1) + k) * (genLeonardo k (t - 1) + k)
        - k * (genLeonardo k m + genLeonardo k n
          - genLeonardo k (m + t) - genLeonardo k (n - t))

/-- The sum-and-difference square identities:
`L_{k,m+n}^2 - L_{k,m-n}^2
= (L_{k,2m+1} + k)(L_{k,2n-1} + k) - 2k (L_{k,m+n} - L_{k,m-n})` and
`L_{k,m+n}^2 + L_{k,m-n-1}^2
= (L_{k,2m} + k)(L_{k,2n} + k) - 2k (L_{k,m+n} + L_{k,m-n-1}) - 2k^2`.

In part (ii) the last summand inside the parenthesis is read as
`L_{k,m-n-1}`. The paper as printed shows `L_{k,m-n}` there, which is
false: at `k = 1, m = 3, n = 1` the printed identity reads `82 = 78`.
The reading used here agrees with the paper's outline derivation and
was verified computationally for `k ∈ {0,1,2,3}`, `m ≤ 11`.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024), Theorem 2.6 (`fq-2024-kuhapatanakul05292024-thm-2.6`). -/
public theorem_wanted genLeonardo_sq_sum_diff (k : ℤ) (m n : ℕ)
    (hn : 1 ≤ n) (hmn : n < m) :
    (genLeonardo k (m + n) ^ 2 - genLeonardo k (m - n) ^ 2
      = (genLeonardo k (2 * m + 1) + k) * (genLeonardo k (2 * n - 1) + k)
        - 2 * k * (genLeonardo k (m + n) - genLeonardo k (m - n))) ∧
    (genLeonardo k (m + n) ^ 2 + genLeonardo k (m - n - 1) ^ 2
      = (genLeonardo k (2 * m) + k) * (genLeonardo k (2 * n) + k)
        - 2 * k * (genLeonardo k (m + n) + genLeonardo k (m - n - 1))
        - 2 * k ^ 2)

/-- The binomial-convolution identities
`∑_i C(n,i) L_{k,i+r} = L_{k,2n+r} - k (2^n - 1)` and
`∑_i C(n,i) M_{k,i+r} = M_{k,2n+r} - 2k (2^n - 1)`.

Parts (iii) and (iv) of the paper's Theorem 3.1 (alternating sums)
are not formalized: as printed they involve the backward index
`L_{k,n-r-2}` and fail, for example at `k = 1, n = 3, r = 1` under
the backward extension (left side `2`, printed right side `-2`).

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024), Theorem 3.1 (i),(ii)
(`fq-2024-kuhapatanakul05292024-thm-3.1`). -/
public theorem_wanted genLeonardo_binomial_sum (k : ℤ) (n r : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * genLeonardo k (i + r)
      = genLeonardo k (2 * n + r) - k * (2 ^ n - 1)) ∧
    (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * genLeonardoCompanion k (i + r)
      = genLeonardoCompanion k (2 * n + r) - 2 * k * (2 ^ n - 1))

/-- The even-order binomial identities
`∑_i C(2m,i) L_{k,2i+r} = 5^m L_{k,2m+r} + k (5^m - 2^{2m})` and
`∑_i C(2m,i) M_{k,2i+r} = 5^m M_{k,2m+r} + 2k (5^m - 2^{2m})`.

This is the even case of the paper's Theorem 3.2; the odd case as
printed is false (at `k = n = 1, r = 0` the first odd identity reads
`4 = 6`) and is not formalized.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024), Theorem 3.2, even case
(`fq-2024-kuhapatanakul05292024-thm-3.2`). -/
public theorem_wanted genLeonardo_binomial_sum_two_mul (k : ℤ) (m r : ℕ) :
    (∑ i ∈ Finset.range (2 * m + 1),
        (Nat.choose (2 * m) i : ℤ) * genLeonardo k (2 * i + r)
      = 5 ^ m * genLeonardo k (2 * m + r) + k * (5 ^ m - 2 ^ (2 * m))) ∧
    (∑ i ∈ Finset.range (2 * m + 1),
        (Nat.choose (2 * m) i : ℤ) * genLeonardoCompanion k (2 * i + r)
      = 5 ^ m * genLeonardoCompanion k (2 * m + r) + 2 * k * (5 ^ m - 2 ^ (2 * m)))

/-- The alternating binomial identities
`∑_i C(n,i) (-1)^{n-i} L_{k,2i+r} = L_{k,n+r} + k` and
`∑_i C(n,i) (-1)^{n-i} M_{k,2i+r} = M_{k,n+r} + 2k`, stated for `n ≥ 1`
(both identities fail at `n = 0` as extracted, where the sums equal
`L_{k,r}` and `M_{k,r}`).

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024), Theorem 3.3 (`fq-2024-kuhapatanakul05292024-thm-3.3`). -/
public theorem_wanted genLeonardo_binomial_alternating (k : ℤ) (n r : ℕ)
    (hn : 1 ≤ n) :
    (∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℤ) * (-1) ^ (n - i) * genLeonardo k (2 * i + r)
      = genLeonardo k (n + r) + k) ∧
    (∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℤ) * (-1) ^ (n - i) * genLeonardoCompanion k (2 * i + r)
      = genLeonardoCompanion k (n + r) + 2 * k)

/-- The step-3 and step-4 binomial identities:
`∑_i C(n,i) L_{k,3i+r} = 2^n L_{k,2n+r}`,
`∑_i C(n,i) M_{k,3i+r} = 2^n M_{k,2n+r}`,
`∑_i C(n,i) L_{k,4i+r} = 3^n L_{k,2n+r} + k (3^n - 2^n)`, and
`∑_i C(n,i) M_{k,4i+r} = 3^n M_{k,2n+r} + 2k (3^n - 2^n)`
(part (iv) as printed in the paper shows `k (3^n - 2^n)`, which is
false at `k = n = 1, r = 0`; the factor `2k` used here is verified
computationally, consistent with parts (ii) of Theorems 3.1–3.3).

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024), Theorem 3.4 (`fq-2024-kuhapatanakul05292024-thm-3.4`). -/
public theorem_wanted genLeonardo_binomial_steps (k : ℤ) (n r : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * genLeonardo k (3 * i + r)
      = 2 ^ n * genLeonardo k (2 * n + r)) ∧
    (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * genLeonardoCompanion k (3 * i + r)
      = 2 ^ n * genLeonardoCompanion k (2 * n + r)) ∧
    (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * genLeonardo k (4 * i + r)
      = 3 ^ n * genLeonardo k (2 * n + r) + k * (3 ^ n - 2 ^ n)) ∧
    (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * genLeonardoCompanion k (4 * i + r)
      = 3 ^ n * genLeonardoCompanion k (2 * n + r) + 2 * k * (3 ^ n - 2 ^ n))

end

end MetaMathlibExt

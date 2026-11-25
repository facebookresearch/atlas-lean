/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Catalan-Larcombe-French numbers

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL27/Zhang/zhang9.tex>.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Catalan–Larcombe–French numbers.** For a natural number $n$, the $n$th
Catalan–Larcombe–French number (OEIS A053175) is
$$
P_n = 2^n \sum_{k=0}^{n} \binom{n}{2k} \binom{2k}{k}^2 4^{n-2k},
$$
where the terms with $2k > n$ vanish because $\binom{n}{2k} = 0$.

Source: concept `jis_sem_503660cf82b130f1605e9f7a`, statement
`jis_1e931a28e8b97599583c6b62`. -/
public def catalanLarcombeFrenchNumber : ℕ → ℕ :=
  fun n => 2 ^ n * Finset.sum (Finset.range (n + 1)) fun k =>
    Nat.choose n (2 * k) * Nat.choose (2 * k) k ^ 2 * 4 ^ (n - 2 * k)

end MetaMathlibExt

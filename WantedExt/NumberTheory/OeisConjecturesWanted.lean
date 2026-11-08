/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Proofs of several conjectures from the OEIS

Statements from Sela Fried, "Proofs of Several
Conjectures From the OEIS", *Journal of Integer
Sequences* 28 (2025), Article 25.4.3
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Fried/fried15.html>).

`avoidZZ1Z k n` counts words of length `n` over a
`k`-letter alphabet with no consecutive pattern
`z, z+1, z`; the recurrence and initial values were
verified by brute force for `k ≤ 4`, `n ≤ 7`. The
bit-length formula was verified for `n ≤ 8`, and the
cube-root floor formula at `n = 3`.

Not stated (see the source audit table): Theorem 1 and
Corollary 2 (the polynomials `B_k^{(m)}` and numbers
`a_{n,k}^{(3)}`), Theorem 4 and Corollary 5 (the
generating function, whose extracted coefficients do
not match the counted sequence), Theorem 8 (median
absolute deviation), and Theorem 9 (whose defining
averaging condition is garbled in the extraction).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Size

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.OeisConjecturesWanted

/-- The number of words of length `n` over the alphabet
`Fin k` avoiding the consecutive pattern `z, z+1, z`:
there is no position `i` with `w (i+2) = w i` and
`w (i+1) = w i + 1` in value. -/
def avoidZZ1Z (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin k)).filter (fun w =>
    ∀ i : Fin n, ∀ h1 : (i : ℕ) + 1 < n,
      ∀ h2 : (i : ℕ) + 2 < n,
        ¬ (w ⟨(i : ℕ) + 2, h2⟩ = w i ∧
          (w ⟨(i : ℕ) + 1, h1⟩ : ℕ) = (w i : ℕ) + 1))).card

/-- **Theorem 3**: the numbers `f_k(n)` of words of
length `n` over a `k`-letter avoiding the pattern
`z, z+1, z` satisfy `f_k(0) = 1`, `f_k(1) = k`,
`f_k(2) = k^2`, and, for `n ≥ 3`,
`f_k(n) = k f_k(n-1) - f_k(n-2) + f_k(n-3)`. The
alphabet is nonempty (`k ≥ 1`); at `k = 0` the recurrence
would read `0 = 1` at `n = 3`.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Theorem 3. -/
theorem_wanted avoidZZ1Z_spec (k : ℕ) (hk : 1 ≤ k) :
    avoidZZ1Z k 0 = 1 ∧ avoidZZ1Z k 1 = k ∧
      avoidZZ1Z k 2 = k ^ 2 ∧
      ∀ n : ℕ, 3 ≤ n →
        (avoidZZ1Z k n : ℤ) =
          (k : ℤ) * avoidZZ1Z k (n - 1) -
            avoidZZ1Z k (n - 2) + avoidZZ1Z k (n - 3)

/-- **Theorem 6**: the number of binary bits required to
represent `C(2^n, 2^{n-1})` is `2^n - ⌊n / 2⌋`.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Theorem 6. -/
theorem_wanted size_choose_two_pow (n : ℕ) (hn : 1 ≤ n) :
    Nat.size (Nat.choose (2 ^ n) (2 ^ (n - 1))) =
      2 ^ n - n / 2

/-- **Theorem 7**: for `n` divisible by `3`, writing
`n = 3m`,
`⌊∑_{i=1}^{10^n} i^{1/3}⌋
  = 3 * 10^{4m} / 4 + 5 * 10^{m-1} - 1`.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Theorem 7. -/
theorem_wanted floor_sum_cbrt (m : ℕ) (hm : 1 ≤ m) :
    Nat.floor (∑ i ∈ Finset.Icc (1 : ℕ) (10 ^ (3 * m)),
        (i : ℝ) ^ (1 / 3 : ℝ)) =
      3 * 10 ^ (4 * m) / 4 + 5 * 10 ^ (m - 1) - 1

end MathlibExt.NumberTheory.OeisConjecturesWanted

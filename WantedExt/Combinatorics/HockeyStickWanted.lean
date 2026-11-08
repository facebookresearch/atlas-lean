/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A generalized hockey stick theorem

Statement from Molly Lynch and Michael Weselcouch, "A
Generalized Hockey Stick Theorem", *Journal of Integer
Sequences* 28 (2025), Article 25.7.7
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Weselcouch/wesel8.html>).

Only Corollary 15 is stated here; Corollary 14 is the
classical hockey stick identity, already in Mathlib as
`Nat.sum_range_add_choose`, and the remaining results
use the paper's lattice-path sequence framework (`Λ`,
labeled sequences, endpoint signs), which is not part
of the extracted statements (see the source audit
table). Corollary 15 was verified numerically for
`n < 8`, `k < 14`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.HockeyStickWanted

/-- **Corollary 15**:
`∑_{i=0}^k C(2i + n, i)
  = ∑_{i=0}^{⌊k/2⌋} (-1)^i C(2k + 1 + n - i, k - 2i)`.

Source: Molly Lynch and Michael Weselcouch, "A
Generalized Hockey Stick Theorem", Corollary 15. -/
theorem_wanted sum_choose_two_mul_add (n k : ℕ) :
    (∑ i ∈ Finset.range (k + 1),
        (Nat.choose (2 * i + n) i : ℤ)) =
      ∑ i ∈ Finset.range (k / 2 + 1),
        (-1 : ℤ) ^ i *
          (Nat.choose (2 * k + 1 + n - i) (k - 2 * i) : ℤ)

end MathlibExt.Combinatorics.HockeyStickWanted

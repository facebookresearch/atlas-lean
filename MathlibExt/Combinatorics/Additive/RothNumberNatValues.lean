/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`SqueezeBench/Problems/Roth/README.md` (leansolving/SqueezeBench):
Copyright the SqueezeBench contributors.
Authors: P. Manrique, H. Xia, S. Szeider.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The statement expresses the values tabulated at commit e2e19eef093a77882da57f348def029533ec2d5e
using Mathlib's Roth number.
-/
module

public import Mathlib.Combinatorics.Additive.AP.Three.Defs

/-!
# Small Roth numbers

At lengths 8, 10, and 12, every subset of size 5, 6, and 7, respectively, contains a
nontrivial three-term progression. We check just those cardinalities. Explicit progression-free
sets give the lower bounds, and extending an interval by one increases its Roth number by at most
one.
-/

namespace MathlibExt.Combinatorics.Additive.ThreeAPFreeValuesWanted

open Finset

private lemma rothNumberNat_le_of_powersetCard {n k : ℕ}
    (h : ∀ s ∈ (range n).powersetCard (k + 1), ¬ThreeAPFree (s : Set ℕ)) :
    rothNumberNat n ≤ k :=
  Nat.le_of_lt_succ (addRothNumber_lt_of_forall_not_threeAPFree h)

private lemma rothNumberNat_eq_between {a b k : ℕ}
    (hl : k ≤ rothNumberNat a) (hu : rothNumberNat b ≤ k)
    (n : ℕ) (ha : a ≤ n) (hb : n ≤ b) : rothNumberNat n = k :=
  ((rothNumberNat.mono hb).trans hu).antisymm (hl.trans (rothNumberNat.mono ha))

-- Use bounded enumeration for the subsets in each upper-bound check.
attribute [local instance 2000] Finset.decidableDforallFinset

/-- **Roth numbers from five to fourteen.** For a natural number $n$, let $r_3(n)$ be the largest
size of a subset of $\{0, 1, \dots, n - 1\}$ containing no three-term arithmetic progression,
that is, no elements $a, b, c$ of the subset with $a + c = 2b$ and $a \neq b$. Then the values
$r_3(5), r_3(6), \dots, r_3(14)$ are $4, 4, 4, 4, 5, 5, 6, 6, 7, 8$, in this order.

Source: OEIS A003002; listed in SqueezeBench
`SqueezeBench/Problems/Roth/README.md`. -/
public theorem rothNumberNat_five_to_fourteen :
    (List.range 10).map (fun i => rothNumberNat (i + 5)) = [4, 4, 4, 4, 5, 5, 6, 6, 7, 8] := by
  have four := rothNumberNat_eq_between (a := 5) (b := 8) (k := 4)
    (ThreeAPFree.le_rothNumberNat {0, 1, 3, 4} (by decide) (by decide) (by decide))
    (rothNumberNat_le_of_powersetCard (by decide +kernel))
  have five := rothNumberNat_eq_between (a := 9) (b := 10) (k := 5)
    (ThreeAPFree.le_rothNumberNat {0, 1, 3, 7, 8} (by decide) (by decide) (by decide))
    (rothNumberNat_le_of_powersetCard (by decide +kernel))
  have six := rothNumberNat_eq_between (a := 11) (b := 12) (k := 6)
    (ThreeAPFree.le_rothNumberNat {0, 1, 3, 4, 9, 10} (by decide) (by decide) (by decide))
    (rothNumberNat_le_of_powersetCard (by decide +kernel))
  have lower : 8 ≤ rothNumberNat 14 :=
    ThreeAPFree.le_rothNumberNat {0, 1, 3, 4, 9, 10, 12, 13} (by decide) (by decide) (by decide)
  have step (n : ℕ) : rothNumberNat (n + 1) ≤ rothNumberNat n + 1 :=
    (rothNumberNat_add_le n 1).trans (Nat.add_le_add_left (rothNumberNat_le 1) _)
  have h₁₂ := six 12 (by decide) (by decide)
  have hu₁₃ : rothNumberNat 13 ≤ rothNumberNat 12 + 1 := step 12
  have hu₁₄ : rothNumberNat 14 ≤ rothNumberNat 13 + 1 := step 13
  have h₁₃ : rothNumberNat 13 = 7 := by omega
  have h₁₄ : rothNumberNat 14 = 8 := by omega
  change [rothNumberNat 5, rothNumberNat 6, rothNumberNat 7, rothNumberNat 8, rothNumberNat 9,
    rothNumberNat 10, rothNumberNat 11, rothNumberNat 12, rothNumberNat 13, rothNumberNat 14] = _
  simp (disch := decide) only [four, five, six, h₁₃, h₁₄]

end MathlibExt.Combinatorics.Additive.ThreeAPFreeValuesWanted

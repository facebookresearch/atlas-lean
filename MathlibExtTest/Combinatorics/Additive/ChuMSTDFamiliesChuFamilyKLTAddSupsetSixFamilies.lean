/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyKLTAddSupsetSixFamilies

namespace MathlibExtTest.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyKLTAddSupsetSixFamilies

open MetaMathlibExt Pointwise

example : ({0, 4, 8, 12, 16, 20, 24, 28, 32} : Finset ℤ) ⊆
    chuFamilyKLT 1 1 1 + chuFamilyKLT 1 1 1 := by
  have h := chuFamilyKLT_add_supset_six_families (k := 1) (l := 1) (t := 1)
    (by decide) (by decide) (by decide)
  simpa [Finset.union_assoc] using h.1

example : Pairwise fun a b : Fin 6 =>
    Disjoint (![{12}, {16}, {20}, {24}, {28}, {32}] a : Finset ℤ)
      (![{12}, {16}, {20}, {24}, {28}, {32}] b) := by
  have h := chuFamilyKLT_add_supset_six_families (k := 1) (l := 1) (t := 1)
    (by decide) (by decide) (by decide)
  simpa using h.2

example : (120 : ℤ) ∈ chuFamilyKLT 2 2 2 + chuFamilyKLT 2 2 2 := by
  have h := chuFamilyKLT_add_supset_six_families (k := 2) (l := 2) (t := 2)
    (by decide) (by decide) (by decide)
  apply h.1
  decide

end MathlibExtTest.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyKLTAddSupsetSixFamilies

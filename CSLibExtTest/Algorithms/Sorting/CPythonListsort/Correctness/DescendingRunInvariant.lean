/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Correctness.DescendingRunInvariant

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

namespace DescendingRunSpec

/-! ## Inhabited regression -/

private def descendingInvariantRegressionLt : BoolComparator Nat :=
  fun left right => decide (left < right)

private theorem descendingInvariantRegressionOrder :
    BoolStrictWeakOrder descendingInvariantRegressionLt := by
  constructor
  let hstrict : IsStrictOrder Nat
      (fun left right => descendingInvariantRegressionLt left right = true) :=
    { irrefl := by simp [descendingInvariantRegressionLt]
      trans := by
        intro a b c hab hbc
        simp [descendingInvariantRegressionLt] at hab hbc ⊢
        omega }
  exact @IsStrictWeakOrder.mk Nat
    (fun left right => descendingInvariantRegressionLt left right = true)
    hstrict (by
      intro a b c hab hbc
      simp [descendingInvariantRegressionLt] at hab hbc ⊢
      omega)

private def descendingInvariantThree : Occurrence Nat :=
  { value := 3, origin := 0 }

private def descendingInvariantTwoOne : Occurrence Nat :=
  { value := 2, origin := 1 }

private def descendingInvariantTwoTwo : Occurrence Nat :=
  { value := 2, origin := 2 }

/-- Concrete strict-then-equivalent regression: the descending scan
`[3@0, 2@1, 2@2]` has an inhabited invariant, and normalization produces the
stable ascending sequence `[2@1, 2@2, 3@0]`.  The proof exercises both public
extension theorems rather than unfolding `Invariant` directly. -/
private theorem descendingRunInvariant_strict_equivalent_regression :
    Invariant descendingInvariantRegressionLt
        [descendingInvariantThree, descendingInvariantTwoOne,
          descendingInvariantTwoTwo]
        [descendingInvariantThree, descendingInvariantTwoOne,
          descendingInvariantTwoTwo] 2 ∧
      normalize
        [descendingInvariantThree, descendingInvariantTwoOne,
          descendingInvariantTwoTwo] 2 =
        [descendingInvariantTwoOne, descendingInvariantTwoTwo,
          descendingInvariantThree] := by
  have hseed := Invariant.singleton descendingInvariantRegressionOrder
    descendingInvariantThree
  have hstrict := hseed.extend_strict descendingInvariantRegressionOrder
    descendingInvariantTwoOne (by
      norm_num [descendingInvariantRegressionLt,
        descendingInvariantThree, descendingInvariantTwoOne])
  have hequivalent :
      ComparatorEquivalent descendingInvariantRegressionLt
        descendingInvariantTwoTwo.value
        ((reverseSuffix [descendingInvariantThree] 1 ++
          [descendingInvariantTwoOne]).getLast (by simp)).value := by
    norm_num [ComparatorEquivalent, descendingInvariantRegressionLt,
      reverseSuffix, descendingInvariantThree, descendingInvariantTwoOne,
      descendingInvariantTwoTwo]
  have horigin :
      ∀ y ∈ [descendingInvariantThree, descendingInvariantTwoOne],
        ComparatorEquivalent descendingInvariantRegressionLt y.value
          descendingInvariantTwoTwo.value →
          y.origin < descendingInvariantTwoTwo.origin := by
    intro y hy hequiv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · norm_num [ComparatorEquivalent, descendingInvariantRegressionLt,
        descendingInvariantThree, descendingInvariantTwoTwo] at hequiv
    · norm_num [descendingInvariantTwoOne, descendingInvariantTwoTwo]
  have hextended := hstrict.extend_equivalent
    descendingInvariantRegressionOrder descendingInvariantTwoTwo
    hequivalent horigin
  constructor
  · simpa [reverseSuffix] using hextended
  · norm_num [normalize, descendingInvariantThree,
      descendingInvariantTwoOne, descendingInvariantTwoTwo]

end DescendingRunSpec

end CPythonListsort

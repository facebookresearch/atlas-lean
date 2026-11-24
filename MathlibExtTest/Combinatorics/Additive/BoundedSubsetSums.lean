/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.BoundedSubsetSums

open MetaMathlibExt

-- With no nonzero entries, the unique admissible subset is the singleton containing zero.
example : boundedSubsetSums 1 0 ({0} : Finset ℤ) = {0} := by decide

-- Two copies of zero can pad either singleton nonzero term to length three.
-- Three copies are forbidden, so zero itself is absent.
example : boundedSubsetSums 2 0
    (Finset.univ.image (Fin.cons 0 ![(-2 : ℤ), 5] : Fin 3 → ℤ)) = {-2, 3, 5} := by
  rw [boundedSubsetSums_eq_generalizedHFoldSumset_of_zero_mem _ (by decide) (by decide)
    2 0 (by decide) (by decide) (by decide)]
  decide

-- When the lower and upper sizes coincide, zero has the same cap as each nonzero element.
example : generalizedHFoldSumset ![(0 : ℤ), -2, 5] (fun _ => 1) 1 = {-2, 0, 5} := by decide

-- A zero lower bound permits the empty subset, even though zero is not a term of the input.
example : boundedSubsetSums 0 1 (Finset.univ.image ![(-2 : ℤ), 5]) = {-2, 0, 5} := by
  rw [boundedSubsetSums_eq_generalizedHFoldSumset_of_zero_not_mem _ (by decide) (by decide)
    0 1 (by decide)]
  decide

-- A positive lower bound excludes the empty subset, while the upper bound permits both entries.
example : boundedSubsetSums 1 0 (Finset.univ.image ![(-2 : ℤ), 5]) = {-2, 3, 5} := by
  rw [boundedSubsetSums_eq_generalizedHFoldSumset_of_zero_not_mem _ (by decide) (by decide)
    1 0 (by decide)]
  decide

private def cycle : Equiv.Perm (Fin 3) :=
  (Equiv.swap 0 1).trans (Equiv.swap 1 2)

example : (cycle 0, cycle 1, cycle 2) = (2, 0, 1) := by decide

-- The three-cycle moves all coordinates, including the one with zero capacity.
example : generalizedHFoldSumset (![-2, 7, (5 : ℤ)] ∘ cycle) (![1, 0, 2] ∘ cycle) 2 =
    {3, 10} := by
  rw [generalizedHFoldSumset_comp_perm]
  decide

-- The empty choice, the fully saturated choice, and an unattainable total.
example : generalizedHFoldSumset (![-2, 7, (5 : ℤ)] ∘ cycle) (![1, 0, 2] ∘ cycle) 0 = {0} := by
  rw [generalizedHFoldSumset_comp_perm]
  decide

example : generalizedHFoldSumset (![-2, 7, (5 : ℤ)] ∘ cycle) (![1, 0, 2] ∘ cycle) 3 = {8} := by
  rw [generalizedHFoldSumset_comp_perm]
  decide

example : generalizedHFoldSumset (![-2, 7, (5 : ℤ)] ∘ cycle) (![1, 0, 2] ∘ cycle) 4 = ∅ := by
  rw [generalizedHFoldSumset_comp_perm]
  decide

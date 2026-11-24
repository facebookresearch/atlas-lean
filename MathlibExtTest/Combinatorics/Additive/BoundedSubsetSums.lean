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

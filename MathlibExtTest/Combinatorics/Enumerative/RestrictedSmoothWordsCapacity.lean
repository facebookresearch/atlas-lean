/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.Combinatorics.Enumerative.RestrictedSmoothWordsCapacity

open MetaMathlibExt

-- Adjacent ones are smooth, but only larger letters may repeat in a restricted word.
example : ![1, 1] ∈ smoothWords 2 ∧ ![1, 1] ∉ restrictedSmoothWords 2 ∧
    ![1, 2, 2] ∈ restrictedSmoothWords 3 := by decide

-- A single column holds no water.
example : (capacityDist (restrictedSmoothWords 1)).natDegree = 0 := by
  have h := restrictedSmoothWords_capacity_natDegree 0 1 (by decide) (by decide)
  norm_num at h
  exact_mod_cast h

-- The two walls of height three in 1232123 trap four cells.
example : wordCapacity ![1, 2, 3, 2, 1, 2, 3] = 4 := by decide

example : (capacityDist (restrictedSmoothWords 7)).natDegree = 4 := by
  have h := restrictedSmoothWords_capacity_natDegree 0 7 (by decide) (by decide)
  norm_num at h
  exact_mod_cast h

-- The negative linear term at residue zero gives five cells, attained by 12321223.
example : wordCapacity ![1, 2, 3, 2, 1, 2, 2, 3] = 5 := by decide

example : (capacityDist (restrictedSmoothWords 8)).natDegree = 5 := by
  have h := restrictedSmoothWords_capacity_natDegree 1 0 (by decide) (by decide)
  norm_num at h
  exact_mod_cast h

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fin.Basic
import MathlibExt.Combinatorics.Enumerative.PermutationStatistics

namespace MetaMathlibExt

/-! Boundary cases: permutations of length below three have none of the four statistics. -/

example : permDoubleAscents (1 : Equiv.Perm (Fin 0)) = 0 ∧
    permPeaks (1 : Equiv.Perm (Fin 0)) = 0 := by
  decide +kernel

example : permDoubleAscents (1 : Equiv.Perm (Fin 2)) = 0 ∧
    permDoubleDescents (Equiv.swap (0 : Fin 2) 1) = 0 ∧
    permPeaks (1 : Equiv.Perm (Fin 2)) = 0 ∧ permValleys (Equiv.swap (0 : Fin 2) 1) = 0 := by
  decide +kernel

/-! Length three: `123`, `321`, `132 = swap 1 2`, `213 = swap 0 1`. -/

example : permDoubleAscents (1 : Equiv.Perm (Fin 3)) = 1 ∧
    permDoubleDescents (1 : Equiv.Perm (Fin 3)) = 0 ∧
    permDoubleDescents (Equiv.swap (0 : Fin 3) 2) = 1 ∧
    permDoubleAscents (Equiv.swap (0 : Fin 3) 2) = 0 := by
  decide +kernel

example : permPeaks (Equiv.swap (1 : Fin 3) 2) = 1 ∧ permValleys (Equiv.swap (1 : Fin 3) 2) = 0 ∧
    permPeaks (Equiv.swap (0 : Fin 3) 1) = 0 ∧ permValleys (Equiv.swap (0 : Fin 3) 1) = 1 := by
  decide +kernel

/-! Length five: the identity has three double ascents; `13254 = swap 1 2 * swap 3 4` has
two peaks (at the first and third positions) and one valley. -/

example : permDoubleAscents (1 : Equiv.Perm (Fin 5)) = 3 := by
  decide +kernel

example : permPeaks (Equiv.swap (1 : Fin 5) 2 * Equiv.swap 3 4) = 2 ∧
    permValleys (Equiv.swap (1 : Fin 5) 2 * Equiv.swap 3 4) = 1 ∧
    permDoubleAscents (Equiv.swap (1 : Fin 5) 2 * Equiv.swap 3 4) = 0 := by
  decide +kernel

/-! Position predicates: `132` peaks at position `0`, `213` has its valley at position `0`, and no
position past `n - 3` carries any local statistic. -/

example : IsPeakAt (Equiv.swap (1 : Fin 3) 2) 0 ∧ IsValleyAt (Equiv.swap (0 : Fin 3) 1) 0 ∧
    ¬ IsDoubleAscentAt (1 : Equiv.Perm (Fin 3)) 1 := by
  decide +kernel

/-- The four counts partition the `n - 2` interior positions. -/
example (σ : Equiv.Perm (Fin 7)) :
    permDoubleAscents σ + permDoubleDescents σ + permPeaks σ + permValleys σ = 5 :=
  permDoubleAscents_add_permDoubleDescents_add_permPeaks_add_permValleys σ

example : ∀ σ : Equiv.Perm (Fin 4),
    permDoubleAscents σ + permDoubleDescents σ + permPeaks σ + permValleys σ = 2 := by
  decide +kernel

/-! Extrema of `13254`: left-to-right maxima `1, 3, 5`; right-to-left maxima `5, 4`; left-to-right
minimum `1`; right-to-left minima `1, 2, 4`. Empty permutation: none. -/

example : permLeftToRightMaxCount (Equiv.swap (1 : Fin 5) 2 * Equiv.swap 3 4) = 3 ∧
    permRightToLeftMaxCount (Equiv.swap (1 : Fin 5) 2 * Equiv.swap 3 4) = 2 ∧
    permLeftToRightMinCount (Equiv.swap (1 : Fin 5) 2 * Equiv.swap 3 4) = 1 ∧
    permRightToLeftMinCount (Equiv.swap (1 : Fin 5) 2 * Equiv.swap 3 4) = 3 := by
  decide +kernel

example : permLeftToRightMaxCount (1 : Equiv.Perm (Fin 0)) = 0 ∧
    permRightToLeftMinCount (1 : Equiv.Perm (Fin 0)) = 0 := by
  decide +kernel

end MetaMathlibExt

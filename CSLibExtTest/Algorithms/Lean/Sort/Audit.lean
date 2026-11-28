/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Sort.Audit

/-!
# Sorting and selection audit checks
-/

open Cslib.Algorithms.Lean.TimeM

#check Cslib.Algorithms.Lean.TimeM.mergeSort_sorted_perm
#check Cslib.Algorithms.Lean.TimeM.mergeSort_comparisons_le
#check Cslib.Algorithms.Lean.TimeM.countingSort_linear_time
#check Cslib.Algorithms.Lean.TimeM.radixSort_linear_time
#check Cslib.Algorithms.Lean.TimeM.medianOfMedians_linear_time

example := mergeSort_sorted_perm [3, 1, 2]

example : ⟪countingSort (fun x => (⟨x % 3, by omega⟩ : Fin 3)) #[2, 0, 1, 2]⟫.toList =
    [0, 1, 2, 2] := by decide

example : ⟪radixSort
    ((fun r : Nat × Nat => ⟨#[(⟨r.1 % 10, by omega⟩ : Fin 10),
      (⟨r.2 % 10, by omega⟩ : Fin 10)], rfl⟩) : (Nat × Nat) → Vector (Fin 10) 2)
    #[(1, 2), (0, 5), (1, 0)] (by decide : 2 ≤ 10)⟫.toList =
    [(0, 5), (1, 0), (1, 2)] := by decide

example : (medianOfMedians [5, 1, 4, 2, 3] 2).ret = some 3 := by decide

#check Cslib.Algorithms.Lean.TimeM.clog_factorial_le

example : Nat.clog 2 (Nat.factorial 5) ≤ 5 * Nat.clog 2 5 := by decide

#check Cslib.Algorithms.Lean.TimeM.countingSort_stable_sorted_perm
#check Cslib.Algorithms.Lean.TimeM.radixSort_stable_sorted_perm
#check Cslib.Algorithms.Lean.TimeM.medianOfMedians_rank

example : ⟪countingSort (fun r => (⟨r.1 % 2, by omega⟩ : Fin 2))
    #[((1 : Nat), 'a'), ((0 : Nat), 'b'), ((1 : Nat), 'c')]⟫.toList =
    [(0, 'b'), (1, 'a'), (1, 'c')] := by decide

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.GeometricTravelingSalesmanDefs
import Mathlib.Data.List.Permutation

namespace MetaMathlibExt.Complexity.NPComplete.GeometricTravelingSalesman

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem dec_bitEncode (i : GeometricTravelingSalesmanInstance) :
    geometricTravelingSalesmanDec (bitEncode i) = true ↔
      WellFormed i ∧ GeometricTravelingSalesmanFeasible i := by
  simp [geometricTravelingSalesmanDec, bitDecode_bitEncode]

/-- The diagonal step between `(0, 0)` and `(1, 1)` has discretized length `⌈√2⌉ = 2`. -/
private theorem discreteDist_diag :
    discreteDist (0, 0) (1, 1) = 2 ∧ discreteDist (1, 1) (0, 0) = 2 := by
  have h : ⌈Real.sqrt 2⌉₊ = 2 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    constructor
    · norm_num
      exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
    · norm_num
  constructor <;> simpa [discreteDist] using h

/-- The two-point tour `(0, 0) → (1, 1) → (0, 0)` has discretized length `2 + 2 = 4 ≤ B = 4`. -/
example :
    geometricTravelingSalesmanDec
      (bitEncode (([((0, 0), (0, 0)), ((1, 0), (1, 0))], 4) :
        GeometricTravelingSalesmanInstance)) = true := by
  rw [dec_bitEncode]
  refine ⟨by unfold WellFormed point toInt; decide, [0, 1], List.Perm.refl _, ?_⟩
  simp [tourLength, point, toInt, List.range_succ, discreteDist_diag.1, discreteDist_diag.2]

/-- The same two points with `B = 3`: the Euclidean tour length `2√2 < 3`, but every tour has
discretized length `4`, so the instance is rejected. -/
example :
    geometricTravelingSalesmanDec
      (bitEncode (([((0, 0), (0, 0)), ((1, 0), (1, 0))], 3) :
        GeometricTravelingSalesmanInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, dec_bitEncode]
  rintro ⟨-, tour, hperm, hlen⟩
  have hmem := List.mem_permutations'.2 hperm
  have hp : (List.range ([((0, 0), (0, 0)), ((1, 0), (1, 0))] :
      List ((ℕ × ℕ) × (ℕ × ℕ))).length).permutations' = [[0, 1], [1, 0]] := by decide
  rw [hp] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl <;>
    simp [tourLength, point, toInt, List.range_succ, discreteDist_diag.1,
      discreteDist_diag.2] at hlen

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := GeometricTravelingSalesmanInstance) bits = none) :
    geometricTravelingSalesmanDec bits = false := by
  simp [geometricTravelingSalesmanDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : geometricTravelingSalesmanDec [true] = false :=
  rejects_undecodable [true] rfl

end MetaMathlibExt.Complexity.NPComplete.GeometricTravelingSalesman

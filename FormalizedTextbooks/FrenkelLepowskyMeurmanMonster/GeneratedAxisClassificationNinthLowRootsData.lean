/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMatrixData

/-! Eight actual preferred short lines encode the complete lower matrix subspace. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators

/-- Original preferred signs and increasing coordinates of the eight lower short lines. -/
def generatedNinthLowRootData : Fin 8 → Fin 2 × Fin 24 × Fin 24 :=
  ![(0, 0, 23), (1, 1, 16), (1, 2, 4), (0, 6, 17),
    (1, 7, 22), (0, 10, 13), (0, 14, 15), (1, 19, 21)]

/-- Unit physical integers of these eight actual orthogonal short lines. -/
def generatedNinthLowRootCoordinates (r : Fin 8) (i : Fin 24) : ℤ :=
  if i = (generatedNinthLowRootData r).2.1 then 1 else
    if i = (generatedNinthLowRootData r).2.2 then
      if (generatedNinthLowRootData r).1 = 0 then -1 else 1
    else 0

/-- The original coordinate pairs are in the actual preferred increasing order. -/
theorem generatedNinthLowRootData_lt : ∀ r : Fin 8,
    (generatedNinthLowRootData r).2.1 < (generatedNinthLowRootData r).2.2 := by
  decide +kernel

/-- The eight original short directions are mutually orthogonal with squared unit norm two. -/
theorem generatedNinth_low_root_gram : ∀ r s : Fin 8,
    (∑ i : Fin 24, generatedNinthLowRootCoordinates r i *
      generatedNinthLowRootCoordinates s i) = if r = s then 2 else 0 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check all 576 matrix entries against the eight original short-coordinate outer products.
/-- The exact original matrix is twelve identity minus twice the eight short outers. -/
theorem generatedNinth_low_root_matrix : ∀ i j : Fin 24,
    generatedNinthMatrixNumerator i j =
      12 * (if i = j then (1 : ℤ) else 0) -
        2 * ∑ r : Fin 8, generatedNinthLowRootCoordinates r i *
          generatedNinthLowRootCoordinates r j := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

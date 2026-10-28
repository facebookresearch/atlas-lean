/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthInverseSpatialCacheActual

/-! Exact whole original matrix transport reuses the certified complete inverse columns. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false

/-- Every original source term is retained; only the full inverse columns are cached. -/
def generatedAxisGlobalOddFourthCachedFramedMatrix (k : Fin 4) : Matrix (Fin 24) (Fin 24) ℚ :=
  fun i j =>
    ∑ u : Fin 24,
      if (generatedAxisGlobalOddFourthInverseSpatialNumerator k u i : ℚ) / 2 = 0 then 0 else
        ∑ v : Fin 24,
          if (generatedAxisGlobalOddFourthInverseSpatialNumerator k v j : ℚ) / 2 = 0 then 0 else
            (generatedAxisGlobalOddFourthOutgoingPacket k).1 u v *
              ((generatedAxisGlobalOddFourthInverseSpatialNumerator k u i : ℚ) / 2) *
                ((generatedAxisGlobalOddFourthInverseSpatialNumerator k v j : ℚ) / 2)

/-- The cached expression equals every coefficient of the entire original framed matrix. -/
theorem generatedAxisGlobalOddFourthCachedFramedMatrix_eq (k : Fin 4) :
    generatedAxisGlobalOddFourthCachedFramedMatrix k = generatedAxisGlobalOddFourthFramedSparseMatrix k := by
  funext i j
  simp only [generatedAxisGlobalOddFourthCachedFramedMatrix,
    generatedAxisGlobalOddFourthFramedSparseMatrix, generatedAxisGlobalRationalSpatialMatrixWordSparse,
    generatedAxisGlobalOddFourthInverseSpatialNumerator_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInteger

/-! Sparse evaluation retains the entire actual positive-Q parity operator. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Skip the parity computation only when the original translated integer coordinate is zero. -/
def generatedNinthPauliSparse (a b : Fin 4096) (v : NortonUIntegerVector) :
    NortonUIntegerVector := fun n =>
  let z := v (generatedSixthSpinLabelXor n a)
  if z = 0 then 0 else
    (if (monsterCo1GeometryBinaryMaskDot 12 b.val n.val).testBit 0 then -1 else 1) * z

/-- Sparse evaluation is exactly the previously proved full signed Q operator. -/
theorem generatedNinth_pauli_sparse (a b : Fin 4096) (v : NortonUIntegerVector) :
    generatedNinthPauliSparse a b v = generatedNinthPauliInteger a b v := by
  ext n
  by_cases h : v (generatedSixthSpinLabelXor n a) = 0 <;>
    simp [generatedNinthPauliSparse, generatedNinthPauliInteger, h]

/-- The sparse integer evaluation retains the actual Q representation. -/
theorem generatedNinth_pauli_sparse_actual (a b : Fin 4096) (v : NortonUIntegerVector) :
    nortonUIntegerQ (generatedNinthPauliQ a b) v = generatedNinthPauliSparse a b v := by
  rw [generatedNinth_pauli_integer, generatedNinth_pauli_sparse]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

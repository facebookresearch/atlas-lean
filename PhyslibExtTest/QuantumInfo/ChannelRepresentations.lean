/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.QuantumInfo.ChannelRepresentations

/-!
# Tests: channel representations (Kraus, Choi, Stinespring)
-/

@[expose] public section

namespace PhyslibExtTest.QuantumInfo.ChannelRepresentations

set_option autoImplicit false

open PhyslibExt.QuantumInfo.Channels

#print axioms exists_cptpMap_iff_kraus
#print axioms exists_cptpMap_iff_choi
#print axioms transposeMap_not_isCompletelyPositive

/-- The transpose example separates positivity from complete positivity on
`Fin 2`: the same map passes one test and fails the other. -/
theorem transposeMap_fin2_positive_not_cp :
    (transposeMap (Fin 2)).IsPositive ∧
      ¬ (transposeMap (Fin 2)).IsCompletelyPositive := by
  constructor
  · first
      | exact transposeMap_isPositive (Fin 2)
      | exact transposeMap_isPositive
  · first
      | exact transposeMap_not_isCompletelyPositive (Fin 2)
      | exact transposeMap_not_isCompletelyPositive

/-- The identity channel has Kraus operators (the general existence
statement at a concrete channel), and they satisfy completeness. -/
theorem id_exists_kraus :
    ∃ K : (Fin 2 × Fin 2) → Matrix (Fin 2) (Fin 2) ℂ,
      (CPTPMap.id (dIn := Fin 2)).map = MatrixMap.of_kraus K K ∧
        ∑ k, (K k).conjTranspose * (K k) = 1 := by
  first
    | exact exists_kraus_of_cptpMap (CPTPMap.id (dIn := Fin 2))
    | exact exists_kraus_of_cptpMap

end PhyslibExtTest.QuantumInfo.ChannelRepresentations

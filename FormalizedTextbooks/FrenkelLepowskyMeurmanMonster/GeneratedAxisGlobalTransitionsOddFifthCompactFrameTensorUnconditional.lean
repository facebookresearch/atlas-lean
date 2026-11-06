/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialPlanActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthCompactFrameTensor

/-! The whole original root-three comparison tensor frames with every source plan discharged. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- Every physical coordinate of both actual original comparison tensor frames is unconditional. -/
theorem generatedAxisGlobalOddFifthCompactFrameTensor_unconditional (k : Fin 2)
    (T : GeneratedAxisGlobalRationalTensor) :
    localTensorRepresentation (generatedAxisGlobalOddFifthComparisonFiber k)
      (generatedAxisGlobalRationalTensorReal T) =
      generatedAxisGlobalRationalTensorReal (generatedAxisGlobalOddFifthCompactFrameTensor k T) :=
  generatedAxisGlobalOddFifthCompactFrameTensor_actual k
    generatedAxisGlobalComparisonMonomialPlans_valid T

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

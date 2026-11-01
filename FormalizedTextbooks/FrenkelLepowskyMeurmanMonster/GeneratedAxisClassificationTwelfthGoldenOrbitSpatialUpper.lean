/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitSorted
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitMetadata
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitCounting

/-! Entire original reachable matrix states give a closed actual spatial stabilizer upper bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The entire actual original Co0 matrix stabilizer has at most 7,372,800 elements. -/
theorem generatedTwelfth_spatial_stabilizer_upper :
    Nat.card generatedTwelfthSpatialStabilizer ≤ 7372800 :=
  generatedTwelfthGoldenOrbit_spatial_upper_of_nodes
    generatedTwelfthGoldenOrbit_nodes generatedTwelfthGoldenMatrixCode_injective
    (fun n => (generatedTwelfthGoldenOrbit_metadata n).1)
    (fun n => (generatedTwelfthGoldenOrbit_metadata n).2)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOctadIndexedData
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOctadCoordinates

/-! Exact source checks for every indexed original octad label and physical coordinate. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxHeartbeats 50000000 in
-- Check all759 complete original twelve-bit code labels.
set_option maxRecDepth 10000 in
/-- Each indexed code is the entire actual original source code label. -/
theorem generatedAxisGlobalOctadIndexedCode_actual (j : Fin 759) :
    generatedAxisGlobalOctadIndexedCode j = generatedAxisGlobalOctadCodeData j := by
  revert j
  decide +kernel

set_option maxHeartbeats 50000000 in
-- Check all6072 physical coordinate positions against the complete original ordered catalogue.
set_option maxRecDepth 10000 in
/-- Every indexed physical coordinate is the actual original catalogue coordinate. -/
theorem generatedAxisGlobalOctadIndexedCoordinate_actual (j : Fin 759) (k : Fin 8) :
    generatedAxisGlobalOctadIndexedCoordinate j k =
      generatedAxisGlobalOctadCoordinatesData j k := by
  revert j k
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

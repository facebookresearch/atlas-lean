/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneOddPackedData

/-! Ordinary-kernel correctness of the compact original code-rank lookup. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Finite source-code bounds are established before they are used as label indices.
/-- Each listed sparse code is an actual valid low source label. -/
theorem generatedSeventhXiOdd_packed_code_bound :
    ∀ g : Fin 232, generatedSeventhXiOddCodes g < 2048 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The 232 literal codes and all packed eight-bit ranks are checked in the ordinary kernel.
/-- Each original listed code has exactly its compact rank. -/
theorem generatedSeventhXiOdd_packed_codes : ∀ g : Fin 232,
    generatedSeventhXiOddPackedInverse
      ⟨generatedSeventhXiOddCodes g, generatedSeventhXiOdd_packed_code_bound g⟩ = g.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The complete 2048-entry lookup uses only bounded shifts of thirty-two literal rows.
/-- Every compact rank gives its genuine code, and absent families retain the explicit sentinel. -/
theorem generatedSeventhXiOdd_packed_inverse : ∀ d : Fin 2048,
    if h : generatedSeventhXiOddPackedInverse d < 232 then
      generatedSeventhXiOddCodes ⟨generatedSeventhXiOddPackedInverse d, h⟩ = d.val
    else generatedSeventhXiOddPackedInverse d = 232 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

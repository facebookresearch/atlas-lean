/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOctadCatalogData

public import Mathlib.Order.Fin.Basic

/-! Exact actual catalogue bindings for all759 original octad code labels. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

-- The literal catalogue has759 entries.
set_option maxRecDepth 10000

set_option maxHeartbeats 20000000 in
-- Check only the758 adjacent original code ranks; strict monotonicity follows generically.
private theorem code_adjacent : ∀ i : Fin 758,
    generatedAxisGlobalOctadCodeData (Fin.castSucc i) <
      generatedAxisGlobalOctadCodeData i.succ := by
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Verify original encoded octad weight for each of the759 candidate code labels.
private theorem code_mem (j : Fin 759) : generatedAxisGlobalOctadCodeData j ∈ golayOctads := by
  have h : ∀ j : Fin 759, generatedAxisGlobalOctadCodeData j ∈ golayOctads := by
    decide +kernel
  exact h j

/-- The displayed finite code is the actual original octad at this catalogue index. -/
theorem generatedAxisGlobalOctadCodeData_actual (j : Fin 759) :
    generatedAxisGlobalOctadCodeData j = golayOctadLabel j := by
  have hm : StrictMono generatedAxisGlobalOctadCodeData :=
    Fin.strictMono_iff_lt_succ.mpr code_adjacent
  have h := Finset.orderEmbOfFin_unique golayOctads_card code_mem hm
  exact congrFun h j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

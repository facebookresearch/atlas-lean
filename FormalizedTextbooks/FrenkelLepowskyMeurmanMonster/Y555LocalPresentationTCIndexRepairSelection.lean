/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact equation indices and lookup for replacement original-source certificates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexRepairContexts

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Literal indices of the 135 equations whose old source references were incorrect. -/
def y322TCIndexRepairIndexRaw : Fin 135 → ℕ :=
  ![
    148825, 148837, 148848, 148860, 148864, 148871, 148882, 148893, 148905, 148917,
    148921, 148929, 148940, 148951, 148963, 148975, 148978, 148986, 148996, 149005,
    149012, 149024, 149026, 149033, 149040, 149048, 149059, 149070, 149074, 149077,
    149087, 149096, 149108, 149116, 149120, 149123, 149130, 149138, 149144, 149153,
    149155, 149160, 149170, 149178, 149184, 149192, 149195, 149199, 149203, 149211,
    149216, 149225, 149227, 149232, 149240, 149251, 149261, 149267, 149271, 149279,
    149291, 149303, 149312, 149321, 149325, 149332, 149344, 149356, 149366, 149375,
    149379, 149386, 149397, 149407, 149424, 149428, 149440, 149448, 149463, 149465,
    149471, 149479, 149486, 149493, 149500, 149505, 149512, 149518, 149523, 149532,
    149539, 149546, 149558, 149566, 149577, 149589, 149596, 149598, 149603, 149608,
    149610, 149615, 149620, 149622, 149628, 149635, 149641, 149643, 149651, 149659,
    149670, 149680, 149690, 149697, 149709, 149717, 149728, 149736, 149746, 149758,
    149773, 149782, 149790, 149799, 149803, 149811, 149819, 149829, 149838, 149844,
    149851, 149861, 149870, 149879, 149882]

/-- All literal replacement indices belong to the unchanged original equation program. -/
theorem y322TCIndexRepairIndexRaw_lt (r : Fin 135) :
    y322TCIndexRepairIndexRaw r < 174819 := by
  revert r
  decide +kernel

/-- The actual original equation index addressed by one replacement certificate. -/
def y322TCIndexRepairIndex (r : Fin 135) : Fin 174819 :=
  ⟨y322TCIndexRepairIndexRaw r, y322TCIndexRepairIndexRaw_lt r⟩

/-- Find an exact replacement index; all other equations retain their original instructions. -/
def y322TCIndexRepairLookup (i : Fin 174819) : Option (Fin 135) :=
  (List.ofFn (fun r : Fin 135 => r)).find? (fun r => decide (y322TCIndexRepairIndex r = i))

/-- Every selected replacement addresses precisely the unchanged equation being checked. -/
theorem y322TCIndexRepairLookup_some (i : Fin 174819) (r : Fin 135)
    (h : y322TCIndexRepairLookup i = some r) : y322TCIndexRepairIndex r = i := by
  exact of_decide_eq_true
    (List.find?_some (p := fun r => decide (y322TCIndexRepairIndex r = i)) h)

/-- No replacement is selected unless its literal index equals the checked equation. -/
theorem y322TCIndexRepairLookup_none (i : Fin 174819)
    (h : y322TCIndexRepairLookup i = none) (r : Fin 135) :
    y322TCIndexRepairIndex r ≠ i := by
  have hn := List.find?_eq_none.mp h r (List.mem_ofFn.mpr ⟨r, rfl⟩)
  simpa only [Bool.not_eq_true, decide_eq_false_iff_not] using hn

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

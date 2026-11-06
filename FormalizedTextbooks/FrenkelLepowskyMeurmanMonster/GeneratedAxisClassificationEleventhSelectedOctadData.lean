/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEleventhPairData

/-! A complete original-packet inverse for the octads needed by genuine selected short witnesses. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Original physical octad catalogue addresses needed by the selected short coefficients. -/
def generatedEleventhSelectedShortOctad : Fin 10 → Fin 759 :=
  ![236, 508, 6, 235, 230, 233, 243, 13, 194, 455]

/-- Exact finite address of a selected octad, with 10 denoting every outside octad. -/
def generatedEleventhSelectedShortOctadIndex (o : Fin 759) : ℕ :=
  if o = 236 then 0 else
  if o = 508 then 1 else
  if o = 6 then 2 else
  if o = 235 then 3 else
  if o = 230 then 4 else
  if o = 233 then 5 else
  if o = 243 then 6 else
  if o = 13 then 7 else
  if o = 194 then 8 else
  if o = 455 then 9 else
  10

/-- The unique original incoming packet number at every selected octad row, or sentinel 4136. -/
def generatedEleventhSelectedOctadSource : Fin 640 → ℕ :=
  ![
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 1196, 1213, 4136, 4136, 301, 0, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 1194, 1211, 4136, 4136, 322, 1, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 342, 4136, 2, 2945, 4136, 4136, 2942, 87, 4136, 281, 4136, 4136, 4136,
  4136, 4136, 4136, 1217, 4136, 1200, 2823, 4136, 4136, 2808, 1209, 4136, 1192, 4136, 4136, 4136,
  4136, 4136, 4136, 3479, 4136, 3474, 1362, 4136, 4136, 1345, 3469, 4136, 3464, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 168, 4136, 4136, 4136, 4136, 181, 4136, 4136, 4136, 4136, 4136,
  3441, 4136, 4136, 1199, 4136, 4136, 3, 4136, 4136, 68, 4136, 4136, 1222, 4136, 4136, 3438,
  3319, 4136, 4136, 299, 4136, 4136, 1208, 4136, 4136, 1201, 4136, 4136, 382, 4136, 4136, 3304,
  518, 4136, 4136, 3348, 4136, 4136, 3476, 4136, 4136, 3467, 4136, 4136, 3339, 4136, 4136, 511,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 362, 4, 4136, 4136, 1255, 1238, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 364, 6, 4136, 4136, 1224, 1241, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 102, 296, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 365, 7, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 366, 8, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 101, 295, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 2511, 4136, 4136, 4136, 4136,
  4136, 3450, 3455, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 13, 371, 4136,
  4136, 376, 18, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 3488, 3493, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 2504, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 2015, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 556, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4073, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 3259, 2071, 4136, 4136, 3396, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 632, 2891, 4136, 4136, 4136, 2772, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 2201, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 809, 4136, 681, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 3575, 4136,
  4136, 4136, 3881, 4136, 3753, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 1876, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136
]

/-- Every original selected octad has exactly its declared finite address. -/
theorem generatedEleventh_selected_octad_index : ∀ s : Fin 10,
    generatedEleventhSelectedShortOctadIndex (generatedEleventhSelectedShortOctad s) = s.val := by
  decide +kernel

/-- Every source is a genuine packet number or the unique outside sentinel. -/
theorem generatedEleventh_selected_octad_source_bound : ∀ p : Fin 640,
    generatedEleventhSelectedOctadSource p ≤ 4136 := by
  decide +kernel

/-- The original selected octad row, with 640 denoting all nonoctad rows. -/
def generatedEleventhIncomingSelectedOctadNumber (n : Fin 4136) : ℕ :=
  match generatedEleventhIncomingShortLabel n with
  | Sum.inr (Sum.inl (o, f)) => 64 * generatedEleventhSelectedShortOctadIndex o + f.val
  | _ => 640

set_option maxHeartbeats 64000000 in
-- Check every original finite packet label against the selected-row inverse.
/-- Every original packet entry reaching a selected octad has exactly its recorded source number. -/
theorem generatedEleventh_selected_octad_source_graph : ∀ n : Fin 4136,
    if h : generatedEleventhIncomingSelectedOctadNumber n < 640 then
      generatedEleventhSelectedOctadSource
        ⟨generatedEleventhIncomingSelectedOctadNumber n, h⟩ = n.val
    else True := by
  decide +kernel

/-- An actual selected octad label identifies the unique original packet source. -/
theorem generatedEleventh_selected_octad_source_forward (n : Fin 4136)
    (s : Fin 10) (f : Fin 64)
    (hn : generatedEleventhIncomingShortLabel n =
      Sum.inr (Sum.inl (generatedEleventhSelectedShortOctad s, f))) :
    generatedEleventhSelectedOctadSource ⟨64 * s.val + f.val, by omega⟩ = n.val := by
  have h := generatedEleventh_selected_octad_source_graph n
  have he : generatedEleventhIncomingSelectedOctadNumber n = 64 * s.val + f.val := by
    simp only [generatedEleventhIncomingSelectedOctadNumber, hn,
      generatedEleventh_selected_octad_index]
  have hb : 64 * s.val + f.val < 640 := by omega
  simpa only [he, hb, dite_eq_left] using h

set_option maxHeartbeats 64000000 in
-- Check every selected original inverse row, including each outside sentinel.
/-- Every nonsentinel selected inverse reconstructs its precise original octad label. -/
theorem generatedEleventh_selected_octad_source_reverse_checked :
    ∀ (s : Fin 10) (f : Fin 64),
      if h : generatedEleventhSelectedOctadSource ⟨64 * s.val + f.val, by omega⟩ < 4136 then
        generatedEleventhIncomingShortLabel
          ⟨generatedEleventhSelectedOctadSource ⟨64 * s.val + f.val, by omega⟩, h⟩ =
            Sum.inr (Sum.inl (generatedEleventhSelectedShortOctad s, f))
      else True := by
  decide +kernel

/-- Every nonsentinel selected inverse retains its exact original physical octad row. -/
theorem generatedEleventh_selected_octad_source_reverse
    (s : Fin 10) (f : Fin 64)
    (h : generatedEleventhSelectedOctadSource ⟨64 * s.val + f.val, by omega⟩ < 4136) :
    generatedEleventhIncomingShortLabel
      ⟨generatedEleventhSelectedOctadSource ⟨64 * s.val + f.val, by omega⟩, h⟩ =
        Sum.inr (Sum.inl (generatedEleventhSelectedShortOctad s, f)) := by
  simpa only [h, dite_eq_left] using generatedEleventh_selected_octad_source_reverse_checked s f

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

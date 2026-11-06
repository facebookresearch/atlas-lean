/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthPairData

/-! A complete original-packet inverse for the octads needed by genuine selected short witnesses. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Original physical octad catalogue addresses needed by the selected short coefficients. -/
def generatedTwelfthSelectedShortOctad : Fin 12 → Fin 759 :=
  ![508, 90, 4, 54, 91, 94, 293, 105, 252, 275, 659, 736]

/-- Exact finite address of a selected octad, with 12 denoting every outside octad. -/
def generatedTwelfthSelectedShortOctadIndex (o : Fin 759) : ℕ :=
  if o = 508 then 0 else
  if o = 90 then 1 else
  if o = 4 then 2 else
  if o = 54 then 3 else
  if o = 91 then 4 else
  if o = 94 then 5 else
  if o = 293 then 6 else
  if o = 105 then 7 else
  if o = 252 then 8 else
  if o = 275 then 9 else
  if o = 659 then 10 else
  if o = 736 then 11 else
  12

/-- The unique original incoming packet number at every selected octad row, or sentinel 4136. -/
def generatedTwelfthSelectedOctadSource : Fin 768 → ℕ :=
  ![
  4136, 4136, 30, 4136, 432, 4136, 180, 183, 4136, 534, 4136, 4136, 4136, 4136, 8, 4136,
  4136, 16, 4136, 4136, 4136, 4136, 458, 4136, 259, 256, 4136, 440, 4136, 38, 4136, 4136,
  29, 4136, 316, 319, 166, 169, 4136, 544, 4136, 4136, 276, 4136, 7, 4136, 294, 297,
  4136, 4136, 42, 4136, 444, 4136, 267, 273, 4136, 454, 4136, 4136, 4136, 4136, 20, 4136,
  4136, 46, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 512, 4136,
  4136, 4136, 4136, 4136, 351, 4136, 4136, 4136, 4136, 4136, 4136, 139, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 474, 242, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 109, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 424, 4136, 4136,
  4136, 4136, 4136, 475, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 247, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 134, 4136, 4136, 4136, 4136, 350, 4136, 4136, 4136, 4136, 4136,
  47, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 508,
  4136, 4136, 4136, 4136, 4136, 4136, 428, 4136, 4136, 91, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 213, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 117, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 143, 189, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 227, 4136, 4136, 4136, 4136, 4136, 4136, 104, 4136, 4136, 4136, 4136,
  4136, 76, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 48, 4136,
  4136, 49, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 188, 4136,
  4136, 4136, 4136, 4136, 501, 4136, 4136, 4136, 4136, 4136, 4136, 496, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 127, 77, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 395, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 373, 4136, 4136,
  4136, 4136, 251, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 86, 4136, 4136,
  4136, 4136, 4136, 4136, 210, 4136, 4136, 4136, 4136, 4136, 4136, 265, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 73, 131, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 146, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 52, 4136,
  4136, 4136, 1444, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 582,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 581, 612,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 584, 553,
  4136, 4136, 4136, 1415, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 554, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 1339, 647, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 1332, 616, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 682, 725, 743, 4136, 4136, 699, 681, 726,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 808, 855,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 1495, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 1448, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 3731, 4136, 4136, 3702, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 2088, 2119, 4136, 2147, 2121, 4136, 2093, 2114
]

/-- Every original selected octad has exactly its declared finite address. -/
theorem generatedTwelfth_selected_octad_index : ∀ s : Fin 12,
    generatedTwelfthSelectedShortOctadIndex (generatedTwelfthSelectedShortOctad s) = s.val := by
  decide +kernel

/-- Every source is a genuine packet number or the unique outside sentinel. -/
theorem generatedTwelfth_selected_octad_source_bound : ∀ p : Fin 768,
    generatedTwelfthSelectedOctadSource p ≤ 4136 := by
  decide +kernel

/-- The original selected octad row, with 768 denoting all nonoctad rows. -/
def generatedTwelfthIncomingSelectedOctadNumber (n : Fin 4136) : ℕ :=
  match generatedTwelfthIncomingShortLabel n with
  | Sum.inr (Sum.inl (o, f)) => 64 * generatedTwelfthSelectedShortOctadIndex o + f.val
  | _ => 768

set_option maxHeartbeats 64000000 in
-- Check every original finite packet label against the selected-row inverse.
/-- Every original packet entry reaching a selected octad has exactly its recorded source number. -/
theorem generatedTwelfth_selected_octad_source_graph : ∀ n : Fin 4136,
    if h : generatedTwelfthIncomingSelectedOctadNumber n < 768 then
      generatedTwelfthSelectedOctadSource
        ⟨generatedTwelfthIncomingSelectedOctadNumber n, h⟩ = n.val
    else True := by
  decide +kernel

/-- An actual selected octad label identifies the unique original packet source. -/
theorem generatedTwelfth_selected_octad_source_forward (n : Fin 4136)
    (s : Fin 12) (f : Fin 64)
    (hn : generatedTwelfthIncomingShortLabel n =
      Sum.inr (Sum.inl (generatedTwelfthSelectedShortOctad s, f))) :
    generatedTwelfthSelectedOctadSource ⟨64 * s.val + f.val, by omega⟩ = n.val := by
  have h := generatedTwelfth_selected_octad_source_graph n
  have he : generatedTwelfthIncomingSelectedOctadNumber n = 64 * s.val + f.val := by
    simp only [generatedTwelfthIncomingSelectedOctadNumber, hn,
      generatedTwelfth_selected_octad_index]
  have hb : 64 * s.val + f.val < 768 := by omega
  simpa only [he, hb, dite_eq_left] using h

set_option maxHeartbeats 64000000 in
-- Check every selected original inverse row, including each outside sentinel.
/-- Every nonsentinel selected inverse reconstructs its precise original octad label. -/
theorem generatedTwelfth_selected_octad_source_reverse_checked :
    ∀ (s : Fin 12) (f : Fin 64),
      if h : generatedTwelfthSelectedOctadSource ⟨64 * s.val + f.val, by omega⟩ < 4136 then
        generatedTwelfthIncomingShortLabel
          ⟨generatedTwelfthSelectedOctadSource ⟨64 * s.val + f.val, by omega⟩, h⟩ =
            Sum.inr (Sum.inl (generatedTwelfthSelectedShortOctad s, f))
      else True := by
  decide +kernel

/-- Every nonsentinel selected inverse retains its exact original physical octad row. -/
theorem generatedTwelfth_selected_octad_source_reverse
    (s : Fin 12) (f : Fin 64)
    (h : generatedTwelfthSelectedOctadSource ⟨64 * s.val + f.val, by omega⟩ < 4136) :
    generatedTwelfthIncomingShortLabel
      ⟨generatedTwelfthSelectedOctadSource ⟨64 * s.val + f.val, by omega⟩, h⟩ =
        Sum.inr (Sum.inl (generatedTwelfthSelectedShortOctad s, f)) := by
  simpa only [h, dite_eq_left] using generatedTwelfth_selected_octad_source_reverse_checked s f

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

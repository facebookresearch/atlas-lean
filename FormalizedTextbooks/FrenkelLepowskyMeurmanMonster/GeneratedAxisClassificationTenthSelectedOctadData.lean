/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthPairData

/-! A complete original-packet inverse for the octads needed by genuine selected short witnesses. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Original physical octad catalogue addresses needed by the selected short coefficients. -/
def generatedTenthSelectedShortOctad : Fin 11 → Fin 759 :=
  ![480, 455, 8, 546, 162, 616, 610, 609, 618, 646, 681]

/-- Exact finite address of a selected octad, with 11 denoting every outside octad. -/
def generatedTenthSelectedShortOctadIndex (o : Fin 759) : ℕ :=
  if o = 480 then 0 else
  if o = 455 then 1 else
  if o = 8 then 2 else
  if o = 546 then 3 else
  if o = 162 then 4 else
  if o = 616 then 5 else
  if o = 610 then 6 else
  if o = 609 then 7 else
  if o = 618 then 8 else
  if o = 646 then 9 else
  if o = 681 then 10 else
  11

/-- The unique original incoming packet number at every selected octad row, or sentinel 4136. -/
def generatedTenthSelectedOctadSource : Fin 704 → ℕ :=
  ![
  4136, 4136, 4136, 4136, 1290, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 0, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 2041, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 581, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 3217, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 1, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 3141, 4136, 1292, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 1296, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 2193, 2,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4101, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 1401,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4099, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 7, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 3139, 4136, 4136, 4136, 1304, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 3929, 4136,
  4136, 4136, 8, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 13, 3450, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 2260, 1641, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 1130, 3127, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 3187, 890, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 1529, 4004, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 3466, 14, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 17, 3434, 4136,
  4136, 4136, 4136, 4136, 4136, 4087, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 2163, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 3493, 18, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 855, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  21, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 1539,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 1977,
  1411, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 1647, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 276, 4136, 4136, 4136, 4136, 4136, 4136, 4136
]

/-- Every original selected octad has exactly its declared finite address. -/
theorem generatedTenth_selected_octad_index : ∀ s : Fin 11,
    generatedTenthSelectedShortOctadIndex (generatedTenthSelectedShortOctad s) = s.val := by
  decide +kernel

/-- Every source is a genuine packet number or the unique outside sentinel. -/
theorem generatedTenth_selected_octad_source_bound : ∀ p : Fin 704,
    generatedTenthSelectedOctadSource p ≤ 4136 := by
  decide +kernel

/-- The original selected octad row, with 704 denoting all nonoctad rows. -/
def generatedTenthIncomingSelectedOctadNumber (n : Fin 4136) : ℕ :=
  match generatedTenthIncomingShortLabel n with
  | Sum.inr (Sum.inl (o, f)) => 64 * generatedTenthSelectedShortOctadIndex o + f.val
  | _ => 704

set_option maxHeartbeats 64000000 in
-- Check every original finite packet label against the selected-row inverse.
/-- Every original packet entry reaching a selected octad has exactly its recorded source number. -/
theorem generatedTenth_selected_octad_source_graph : ∀ n : Fin 4136,
    if h : generatedTenthIncomingSelectedOctadNumber n < 704 then
      generatedTenthSelectedOctadSource
        ⟨generatedTenthIncomingSelectedOctadNumber n, h⟩ = n.val
    else True := by
  decide +kernel

/-- An actual selected octad label identifies the unique original packet source. -/
theorem generatedTenth_selected_octad_source_forward (n : Fin 4136)
    (s : Fin 11) (f : Fin 64)
    (hn : generatedTenthIncomingShortLabel n =
      Sum.inr (Sum.inl (generatedTenthSelectedShortOctad s, f))) :
    generatedTenthSelectedOctadSource ⟨64 * s.val + f.val, by omega⟩ = n.val := by
  have h := generatedTenth_selected_octad_source_graph n
  have he : generatedTenthIncomingSelectedOctadNumber n = 64 * s.val + f.val := by
    simp only [generatedTenthIncomingSelectedOctadNumber, hn,
      generatedTenth_selected_octad_index]
  have hb : 64 * s.val + f.val < 704 := by omega
  simpa only [he, hb, dite_eq_left] using h

set_option maxHeartbeats 64000000 in
-- Check every selected original inverse row, including each outside sentinel.
/-- Every nonsentinel selected inverse reconstructs its precise original octad label. -/
theorem generatedTenth_selected_octad_source_reverse_checked :
    ∀ (s : Fin 11) (f : Fin 64),
      if h : generatedTenthSelectedOctadSource ⟨64 * s.val + f.val, by omega⟩ < 4136 then
        generatedTenthIncomingShortLabel
          ⟨generatedTenthSelectedOctadSource ⟨64 * s.val + f.val, by omega⟩, h⟩ =
            Sum.inr (Sum.inl (generatedTenthSelectedShortOctad s, f))
      else True := by
  decide +kernel

/-- Every nonsentinel selected inverse retains its exact original physical octad row. -/
theorem generatedTenth_selected_octad_source_reverse
    (s : Fin 11) (f : Fin 64)
    (h : generatedTenthSelectedOctadSource ⟨64 * s.val + f.val, by omega⟩ < 4136) :
    generatedTenthIncomingShortLabel
      ⟨generatedTenthSelectedOctadSource ⟨64 * s.val + f.val, by omega⟩, h⟩ =
        Sum.inr (Sum.inl (generatedTenthSelectedShortOctad s, f)) := by
  simpa only [h, dite_eq_left] using generatedTenth_selected_octad_source_reverse_checked s f

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

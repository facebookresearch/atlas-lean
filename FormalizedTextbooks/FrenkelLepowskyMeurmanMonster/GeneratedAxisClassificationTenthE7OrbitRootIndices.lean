/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2RootCatalog

/-! The exact sixty-three addresses in the original complete E8 root catalogue
perpendicular to the standard root e4+e5. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxRecDepth 100000

/-- Original E8 catalogue addresses of all perpendicular E7 root lines. -/
def generatedTenthE7OrbitRootIndex : Fin 63 → Fin 120 :=
  ![0, 1, 2, 5, 6, 7, 8, 11, 12, 13, 16, 17,
    20, 21, 22, 27, 28, 29, 30, 33, 34, 35, 36, 39,
    40, 41, 44, 45, 48, 49, 55, 72, 73, 74, 75, 76,
    77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88,
    89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100,
    101, 102, 103]

/-- The complete perpendicular subset of the already certified local E8 catalogue. -/
def generatedTenthE7OrbitRootIndices : Finset (Fin 120) :=
  Finset.univ.filter fun r => leechSeventhE8RootLocal r 4 + leechSeventhE8RootLocal r 5 = 0

/-- The complete perpendicular subset has exactly sixty-three addresses. -/
theorem generatedTenth_e7_orbit_root_indices_card : generatedTenthE7OrbitRootIndices.card = 63 := by
  decide +kernel

/-- Every selected address is perpendicular to the actual standard normal root. -/
theorem generatedTenth_e7_orbit_root_index_mem : ∀ r : Fin 63,
    generatedTenthE7OrbitRootIndex r ∈ generatedTenthE7OrbitRootIndices := by
  decide +kernel

/-- No selected original E8-catalogue address is repeated. -/
theorem generatedTenth_e7_orbit_root_index_injective :
    Function.Injective generatedTenthE7OrbitRootIndex := by
  decide +kernel

/-- Every perpendicular original E8-catalogue address is among the selected ones. -/
def generatedTenthE7OrbitRootIndexEquiv : Fin 63 ≃ generatedTenthE7OrbitRootIndices :=
  Equiv.ofBijective
    (fun r => ⟨generatedTenthE7OrbitRootIndex r, generatedTenth_e7_orbit_root_index_mem r⟩)
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨by
      intro r s h
      exact generatedTenth_e7_orbit_root_index_injective (congrArg Subtype.val h), by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_coe] using
        generatedTenth_e7_orbit_root_indices_card.symm⟩)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

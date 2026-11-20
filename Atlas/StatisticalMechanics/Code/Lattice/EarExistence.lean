/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.TurningNumber
import Code.Lattice.CornerBalance
import Code.Lattice.EarRemoval

open SimpleGraph Function

namespace StatMech

namespace Lattice










theorem unitWt_negx : unitWt (![-1, 0] : Site 2) = 1 := by simp [unitWt, Fin.sum_univ_two]




noncomputable def leftDart (c : Site 2) : Dart := mkDart c ![-1, 0] unitWt_negx

@[simp] theorem leftDart_tail (c : Site 2) : (leftDart c).tail = c := rfl

theorem leftDart_dir (c : Site 2) : (leftDart c).dir = ![-1, 0] := by
  rw [leftDart, mkDart_dir]

theorem leftDart_head (c : Site 2) : (leftDart c).head = c + ![-1, 0] := by
  rw [leftDart, mkDart_head]



theorem leftDart_travel (c : Site 2) : -rot90Fun (leftDart c).dir = ![0, 1] := by
  rw [leftDart_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp


theorem leftDart_head_coord0 (c : Site 2) : (leftDart c).head 0 = c 0 - 1 := by
  rw [leftDart_head, Pi.add_apply]; simp; ring


theorem leftDart_head_coord1 (c : Site 2) : (leftDart c).head 1 = c 1 := by
  rw [leftDart_head, Pi.add_apply]; simp


theorem leftDart_front_coord0 (c : Site 2) :
    ((leftDart c).head + (-rot90Fun (leftDart c).dir)) 0 = c 0 - 1 := by
  rw [leftDart_travel, Pi.add_apply, leftDart_head_coord0]; simp



theorem leftDart_front_coord1 (c : Site 2) :
    ((leftDart c).head + (-rot90Fun (leftDart c).dir)) 1 = c 1 + 1 := by
  rw [leftDart_travel, Pi.add_apply, leftDart_head_coord1]; simp


theorem leftDart_side_coord0 (c : Site 2) :
    ((leftDart c).tail + (-rot90Fun (leftDart c).dir)) 0 = c 0 := by
  rw [leftDart_travel, Pi.add_apply, leftDart_tail]; simp



theorem leftDart_side_coord1 (c : Site 2) :
    ((leftDart c).tail + (-rot90Fun (leftDart c).dir)) 1 = c 1 + 1 := by
  rw [leftDart_travel, Pi.add_apply, leftDart_tail]; simp












noncomputable def lexKey (v : Site 2) : ℤ ×ₗ ℤ := toLex (v 1, - v 0)



structure IsExtremeCell (K : Set (Site 2)) (c : Site 2) : Prop where
  
  mem : c ∈ K
  
  maximal : ∀ v ∈ K, lexKey v ≤ lexKey c




theorem exists_extremeCell (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ c, IsExtremeCell K c := by
  have hfne : hK.toFinset.Nonempty := by rwa [Set.Finite.toFinset_nonempty]
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image hK.toFinset lexKey hfne
  refine ⟨c, ⟨by rwa [Set.Finite.mem_toFinset] at hc, ?_⟩⟩
  intro v hv
  exact hmax v (by rwa [Set.Finite.mem_toFinset])



theorem extremeCell_not_mem_of_higher (K : Set (Site 2)) (c v : Site 2)
    (hc : IsExtremeCell K c) (hy : c 1 < v 1) : v ∉ K := by
  intro hv
  have h := hc.maximal v hv
  unfold lexKey at h
  rw [Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h1, h2⟩ <;> omega




theorem extremeCell_not_mem_of_left (K : Set (Site 2)) (c v : Site 2)
    (hc : IsExtremeCell K c) (hy : v 1 = c 1) (hx : v 0 < c 0) : v ∉ K := by
  intro hv
  have h := hc.maximal v hv
  unfold lexKey at h
  rw [Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h1, h2⟩ <;> omega









theorem extremeCell_front_nmem (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    (leftDart c).head + (-rot90Fun (leftDart c).dir) ∉ K := by
  apply extremeCell_not_mem_of_higher K c _ hc
  rw [leftDart_front_coord1]; omega



theorem extremeCell_side_nmem (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    (leftDart c).tail + (-rot90Fun (leftDart c).dir) ∉ K := by
  apply extremeCell_not_mem_of_higher K c _ hc
  rw [leftDart_side_coord1]; omega



theorem extremeCell_head_nmem (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    (leftDart c).head ∉ K := by
  apply extremeCell_not_mem_of_left K c _ hc
  · rw [leftDart_head_coord1]
  · rw [leftDart_head_coord0]; omega




theorem extremeCell_boundary (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    IsBoundaryDart K (leftDart c) :=
  ⟨by rw [leftDart_tail]; exact hc.mem, extremeCell_head_nmem K c hc⟩






theorem extremeCell_turnZ (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    turnZ K (leftDart c) = -1 := by
  unfold turnZ
  rw [if_neg (extremeCell_front_nmem K c hc), if_neg (extremeCell_side_nmem K c hc)]






theorem exists_convex_corner_dart (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ e : Dart, IsBoundaryDart K e ∧ turnZ K e = -1 := by
  obtain ⟨c, hc⟩ := exists_extremeCell K hK hne
  exact ⟨leftDart c, extremeCell_boundary K c hc, extremeCell_turnZ K c hc⟩











theorem one_le_leftCornerCount_of_first (K : Set (Site 2)) (e : Dart) (p : ℕ) (hp : 0 < p)
    (h0 : turnZ K e = -1) : 1 ≤ leftCornerCount K e p := by
  classical
  unfold leftCornerCount
  have hmem : 0 ∈ (Finset.range p).filter (fun i => turnZ K ((dartNext K)^[i] e) = -1) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hp, by rw [Function.iterate_zero_apply]; exact h0⟩
  have : 1 ≤ ((Finset.range p).filter
      (fun i => turnZ K ((dartNext K)^[i] e) = -1)).card :=
    Finset.card_pos.mpr ⟨0, hmem⟩
  exact_mod_cast this




noncomputable def extremeBase (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    {e : Dart // IsBoundaryDart K e} :=
  ⟨leftDart c, extremeCell_boundary K c hc⟩





theorem extremeCell_orbit_one_le_leftCornerCount (K : Set (Site 2)) (hK : K.Finite)
    (c : Site 2) (hc : IsExtremeCell K c) :
    1 ≤ leftCornerCount K (extremeBase K c hc).1 (dartOrbitPeriod K (extremeBase K c hc)) := by
  apply one_le_leftCornerCount_of_first
  · exact dartOrbitPeriod_pos K hK (extremeBase K c hc)
  · show turnZ K (leftDart c) = -1
    exact extremeCell_turnZ K c hc





theorem extremeCell_orbit_rightCornerCount_lt_period (K : Set (Site 2)) (hK : K.Finite)
    (c : Site 2) (hc : IsExtremeCell K c) :
    rightCornerCount K (extremeBase K c hc).1 (dartOrbitPeriod K (extremeBase K c hc)) <
      (dartOrbitPeriod K (extremeBase K c hc) : ℤ) := by
  have hpart := orbitStep_partition K (extremeBase K c hc).1 (dartOrbitPeriod K (extremeBase K c hc))
  have hleft := extremeCell_orbit_one_le_leftCornerCount K hK c hc
  have hstraight : (0 : ℤ) ≤ straightStepCount K (extremeBase K c hc).1
      (dartOrbitPeriod K (extremeBase K c hc)) := by
    unfold straightStepCount; positivity
  linarith










theorem removeCell_finite (K : Set (Site 2)) (hK : K.Finite) (c : Site 2) :
    (K \ {c}).Finite :=
  hK.subset Set.diff_subset





theorem removeCell_ncard_lt (K : Set (Site 2)) (hK : K.Finite) (c : Site 2) (hc : c ∈ K) :
    (K \ {c}).ncard < K.ncard := by
  have hsub : (K \ {c}) ⊂ K := by
    rw [Set.ssubset_iff_of_subset Set.diff_subset]
    exact ⟨c, hc, by simp⟩
  exact Set.ncard_lt_ncard hsub hK




theorem removeExtremeCell_ncard_lt (K : Set (Site 2)) (hK : K.Finite) (c : Site 2)
    (hc : IsExtremeCell K c) : (K \ {c}).ncard < K.ncard :=
  removeCell_ncard_lt K hK c hc.mem































end Lattice

end StatMech

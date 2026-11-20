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
import Code.Lattice.DartOrbit

open SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice





def kc2_dirSet : Finset (Site 2) :=
  {![1, 0], ![-1, 0], ![0, 1], ![0, -1]}


theorem kc2_mem_dirSet (d : Site 2) :
    d ∈ kc2_dirSet ↔ d = ![1, 0] ∨ d = ![-1, 0] ∨ d = ![0, 1] ∨ d = ![0, -1] := by
  simp only [kc2_dirSet, Finset.mem_insert, Finset.mem_singleton]


theorem kc2_dirSet_card : kc2_dirSet.card = 4 := by
  rw [kc2_dirSet]
  decide


theorem kc2_unitWt_cardinal :
    unitWt (![1, 0] : Site 2) = 1 ∧ unitWt (![-1, 0] : Site 2) = 1 ∧
      unitWt (![0, 1] : Site 2) = 1 ∧ unitWt (![0, -1] : Site 2) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · unfold unitWt
      rw [Fin.sum_univ_two]
      decide






theorem kc2_unitWt_one_cases (d : Site 2) (hd : unitWt d = 1) :
    d = ![1, 0] ∨ d = ![-1, 0] ∨ d = ![0, 1] ∨ d = ![0, -1] := by
  unfold unitWt at hd
  rw [Fin.sum_univ_two] at hd
  
  have key : ((d 0).natAbs = 1 ∧ (d 1).natAbs = 0) ∨ ((d 0).natAbs = 0 ∧ (d 1).natAbs = 1) := by
    omega
  rcases key with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · 
    have hb' : d 1 = 0 := Int.natAbs_eq_zero.mp hb
    rcases Int.natAbs_eq_iff.mp ha with h | h
    · exact Or.inl (by funext i; fin_cases i <;> simp [h, hb'])
    · exact Or.inr (Or.inl (by funext i; fin_cases i <;> simp [h, hb']))
  · 
    have ha' : d 0 = 0 := Int.natAbs_eq_zero.mp ha
    rcases Int.natAbs_eq_iff.mp hb with h | h
    · exact Or.inr (Or.inr (Or.inl (by funext i; fin_cases i <;> simp [ha', h])))
    · exact Or.inr (Or.inr (Or.inr (by funext i; fin_cases i <;> simp [ha', h])))


theorem kc2_unitWt_one_mem_dirSet (d : Site 2) (hd : unitWt d = 1) : d ∈ kc2_dirSet :=
  (kc2_mem_dirSet d).mpr (kc2_unitWt_one_cases d hd)




theorem kc2_unitWt_one_rec {P : Prop} (d : Site 2) (hd : unitWt d = 1)
    (h0 : d = ![1, 0] → P) (h1 : d = ![-1, 0] → P)
    (h2 : d = ![0, 1] → P) (h3 : d = ![0, -1] → P) : P := by
  rcases kc2_unitWt_one_cases d hd with h | h | h | h
  · exact h0 h
  · exact h1 h
  · exact h2 h
  · exact h3 h





theorem kc2_dart_dir_cases (e : Dart) :
    e.dir = ![1, 0] ∨ e.dir = ![-1, 0] ∨ e.dir = ![0, 1] ∨ e.dir = ![0, -1] :=
  kc2_unitWt_one_cases e.dir (unitWt_dir e)


theorem kc2_dart_dir_mem_dirSet (e : Dart) : e.dir ∈ kc2_dirSet :=
  kc2_unitWt_one_mem_dirSet e.dir (unitWt_dir e)



theorem kc2_dart_dir_rec {P : Prop} (e : Dart)
    (h0 : e.dir = ![1, 0] → P) (h1 : e.dir = ![-1, 0] → P)
    (h2 : e.dir = ![0, 1] → P) (h3 : e.dir = ![0, -1] → P) : P :=
  kc2_unitWt_one_rec e.dir (unitWt_dir e) h0 h1 h2 h3





theorem kc2_orbit_dart_iterate (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {b : {e : Dart // IsBoundaryDart K e}} (hb : b ∈ (dartOrbitWalk K a).support) :
    ∃ k, (dartNextSub K)^[k] a = b := by
  rw [dartOrbitWalk_support, List.mem_map] at hb
  obtain ⟨k, _, hk⟩ := hb
  exact ⟨k, hk⟩




theorem kc2_orbit_dir_cases (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {b : {e : Dart // IsBoundaryDart K e}} (_hb : b ∈ (dartOrbitWalk K a).support) :
    b.1.dir = ![1, 0] ∨ b.1.dir = ![-1, 0] ∨ b.1.dir = ![0, 1] ∨ b.1.dir = ![0, -1] :=
  kc2_dart_dir_cases b.1



theorem kc2_orbit_dir_mem_dirSet (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {b : {e : Dart // IsBoundaryDart K e}} (_hb : b ∈ (dartOrbitWalk K a).support) :
    b.1.dir ∈ kc2_dirSet :=
  kc2_dart_dir_mem_dirSet b.1




theorem kc2_orbit_dir_rec {P : Prop} (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {b : {e : Dart // IsBoundaryDart K e}} (hb : b ∈ (dartOrbitWalk K a).support)
    (h0 : b.1.dir = ![1, 0] → P) (h1 : b.1.dir = ![-1, 0] → P)
    (h2 : b.1.dir = ![0, 1] → P) (h3 : b.1.dir = ![0, -1] → P) : P := by
  rcases kc2_orbit_dir_cases K a hb with h | h | h | h
  · exact h0 h
  · exact h1 h
  · exact h2 h
  · exact h3 h









theorem kc2_mkDart_dir_cardinal :
    (mkDart 0 (![1, 0] : Site 2) kc2_unitWt_cardinal.1).dir = ![1, 0] := by
  rw [mkDart_dir]

end Walls

end StatMech

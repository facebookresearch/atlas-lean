/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.Clusters
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartOrbit
import Code.Lattice.TurningNumber
import Code.Lattice.UmlaufsatzSingleCycle
import Code.Lattice.WindingWitness
import Code.Lattice.NoDiagTouchClose

open SimpleGraph Function Set Finset

namespace StatMech

namespace Walls

open StatMech.Lattice











theorem jwd_untouched_localTurn_zero (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (f : Site 2)
    (h : usc_visitSet K a f = ∅) :
    usc_localTurn K a f = 0 := by
  unfold usc_localTurn
  rw [h, Finset.sum_empty]







theorem jwd_touched_localTurn_eq_lone_turnZ (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hmult : usc_FaceMultiplicityOne K a)
    (f : Site 2) (hne : (usc_visitSet K a f).Nonempty) :
    ∃ i, usc_visitSet K a f = {i} ∧
      usc_localTurn K a f = turnZ K ((dartNext K)^[i] a.1) := by
  
  have hpos : 1 ≤ (usc_visitSet K a f).card := Finset.Nonempty.card_pos hne
  have hcard1 : (usc_visitSet K a f).card = 1 := hmult f hpos
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard1
  exact ⟨i, hi, usc_singleVisit_local_turn K a f i hi⟩




theorem jwd_turnZ_window (K : Set (Site 2)) (e : Dart) :
    turnZ K e = 1 ∨ turnZ K e = 0 ∨ turnZ K e = -1 :=
  turnZ_mem K e










theorem jwd_localTurn_mem (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hmult : usc_FaceMultiplicityOne K a) (f : Site 2) :
    usc_localTurn K a f = 1 ∨ usc_localTurn K a f = 0 ∨ usc_localTurn K a f = -1 := by
  classical
  rcases (usc_visitSet K a f).eq_empty_or_nonempty with h0 | hne
  · 
    right; left
    exact jwd_untouched_localTurn_zero K a f h0
  · 
    obtain ⟨i, _, heq⟩ := jwd_touched_localTurn_eq_lone_turnZ K a hmult f hne
    rw [heq]
    exact jwd_turnZ_window K _












theorem jwd_starHull_touched_localTurn_eq_lone_turnZ (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) (f : Site 2)
    (hne : (usc_visitSet (ndt_StarHull K) a f).Nonempty) :
    ∃ i, usc_visitSet (ndt_StarHull K) a f = {i} ∧
      usc_localTurn (ndt_StarHull K) a f =
        turnZ (ndt_StarHull K) ((dartNext (ndt_StarHull K))^[i] a.1) :=
  jwd_touched_localTurn_eq_lone_turnZ (ndt_StarHull K) a (ndt_faceMultiplicityOne K a) f hne






theorem jwd_starHull_localTurn_mem (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) (f : Site 2) :
    usc_localTurn (ndt_StarHull K) a f = 1 ∨ usc_localTurn (ndt_StarHull K) a f = 0 ∨
      usc_localTurn (ndt_StarHull K) a f = -1 :=
  jwd_localTurn_mem (ndt_StarHull K) a (ndt_faceMultiplicityOne K a) f

end Walls

end StatMech

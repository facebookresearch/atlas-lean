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
import Code.Lattice.TurningNumber
import Code.Lattice.BalancePreservingContraction
import Code.Walls.jc_steplocal
import Code.Walls.jc3_earfootprint

open SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice














theorem jc4_notProbed_of_avoidsEarFootprint (r : Site 2) (e : Dart)
    (h : jc3_AvoidsEarFootprint r e) : bpc_NotProbed r e :=
  jc3_notProbed_of_avoidsEarFootprint r e h







theorem jc4_dartNext_eq_of_avoidsEarFootprint (K : Set (Site 2)) (r : Site 2) (e : Dart)
    (h : jc3_AvoidsEarFootprint r e) :
    dartNext (K \ {r}) e = dartNext K e :=
  bpc_dartNext_diff_singleton K r e (jc4_notProbed_of_avoidsEarFootprint r e h)





theorem jc4_turnZ_eq_of_avoidsEarFootprint (K : Set (Site 2)) (r : Site 2) (e : Dart)
    (h : jc3_AvoidsEarFootprint r e) :
    turnZ (K \ {r}) e = turnZ K e :=
  bpc_turnZ_diff_singleton K r e (jc4_notProbed_of_avoidsEarFootprint r e h)

















theorem jc4_footprintAgree (K : Set (Site 2)) (r : Site 2) (e : Dart)
    (h : jc3_AvoidsEarFootprint r e) :
    bpc_NotProbed r e ∧
      dartNext (K \ {r}) e = dartNext K e ∧
      turnZ (K \ {r}) e = turnZ K e :=
  ⟨jc4_notProbed_of_avoidsEarFootprint r e h,
   jc4_dartNext_eq_of_avoidsEarFootprint K r e h,
   jc4_turnZ_eq_of_avoidsEarFootprint K r e h⟩














theorem jc4_footprintAgree_full (K : Set (Site 2)) (r : Site 2) (e : Dart)
    (h : jc3_AvoidsEarFootprint r e) :
    bpc_NotProbed r e ∧
      dartNext (K \ {r}) e = dartNext K e ∧
      turnZ (K \ {r}) e = turnZ K e ∧
      turn (K \ {r}) e = turn K e := by
  have hnp : bpc_NotProbed r e := jc4_notProbed_of_avoidsEarFootprint r e h
  obtain ⟨hnp1, hnp2⟩ := hnp
  
  have hstep := jc_step_local (K \ {r}) K e ?_ ?_
  · exact ⟨⟨hnp1, hnp2⟩, hstep.1, hstep.2.1, hstep.2.2⟩
  · constructor
    · intro hmem; exact (Set.mem_diff _).mp hmem |>.1
    · intro hmem
      refine (Set.mem_diff _).mpr ⟨hmem, ?_⟩
      simp only [Set.mem_singleton_iff]
      exact hnp1
  · constructor
    · intro hmem; exact (Set.mem_diff _).mp hmem |>.1
    · intro hmem
      refine (Set.mem_diff _).mpr ⟨hmem, ?_⟩
      simp only [Set.mem_singleton_iff]
      exact hnp2




















theorem jc4_footprintAgree_orbit (K : Set (Site 2)) (r : Site 2) (e : Dart)
    (hfoot : ∀ i, jc3_AvoidsEarFootprint r ((dartNext K)^[i] e)) (i : ℕ) :
    bpc_NotProbed r ((dartNext K)^[i] e) ∧
      dartNext (K \ {r}) ((dartNext K)^[i] e) = dartNext K ((dartNext K)^[i] e) ∧
      turnZ (K \ {r}) ((dartNext K)^[i] e) = turnZ K ((dartNext K)^[i] e) :=
  jc4_footprintAgree K r ((dartNext K)^[i] e) (hfoot i)











theorem jc4_farDart_footprintAgree (K : Set (Site 2)) :
    bpc_NotProbed (![0, 0] : Site 2) jc3_farDart ∧
      dartNext (K \ {(![0, 0] : Site 2)}) jc3_farDart = dartNext K jc3_farDart ∧
      turnZ (K \ {(![0, 0] : Site 2)}) jc3_farDart = turnZ K jc3_farDart :=
  jc4_footprintAgree K (![0, 0] : Site 2) jc3_farDart jc3_farDart_avoidsOrigin

























end Walls

end StatMech

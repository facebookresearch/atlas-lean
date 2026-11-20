/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































































import Mathlib
import Code.Lattice.BalancePreservingContraction
import Code.Walls.jc3_core

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice




















theorem jc4_iterate_coincide (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (hnp : ∀ i, bpc_NotProbed r ((dartNext K)^[i] a.1)) (k : ℕ) :
    (dartNext (K \ {r}))^[k] a.1 = (dartNext K)^[k] a.1 :=
  bpc_iterate_dartNext_diff_singleton K r a.1 hnp k





theorem jc4_basepoint_survives (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (hne : r ≠ a.1.tail) : IsBoundaryDart (K \ {r}) a.1 :=
  bpc_isBoundaryDart_diff_singleton K r a.1 a.2 hne











theorem jc4_period_eq (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (hnp : ∀ i, bpc_NotProbed r ((dartNext K)^[i] a.1)) (hne : r ≠ a.1.tail) :
    dartOrbitPeriod (K \ {r}) ⟨a.1, jc4_basepoint_survives K a r hne⟩ = dartOrbitPeriod K a :=
  bpc_dartOrbitPeriod_diff_singleton K r a ⟨a.1, jc4_basepoint_survives K a r hne⟩ rfl hnp






theorem jc4_iterate_coincide_and_period_eq (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hnp : ∀ i, bpc_NotProbed r ((dartNext K)^[i] a.1)) (hne : r ≠ a.1.tail) :
    ∃ a' : {e : Dart // IsBoundaryDart (K \ {r}) e},
      a'.1 = a.1 ∧
      (∀ k, (dartNext (K \ {r}))^[k] a'.1 = (dartNext K)^[k] a.1) ∧
      dartOrbitPeriod (K \ {r}) a' = dartOrbitPeriod K a := by
  refine ⟨⟨a.1, jc4_basepoint_survives K a r hne⟩, rfl, ?_, ?_⟩
  · intro k; exact jc4_iterate_coincide K a r hnp k
  · exact jc4_period_eq K a r hnp hne


















theorem jc4_turn_coincide (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (hnp : ∀ i, bpc_NotProbed r ((dartNext K)^[i] a.1)) (i : ℕ) :
    turnZ (K \ {r}) ((dartNext (K \ {r}))^[i] a.1) = turnZ K ((dartNext K)^[i] a.1) := by
  rw [jc4_iterate_coincide K a r hnp i]
  exact bpc_turnZ_diff_singleton K r ((dartNext K)^[i] a.1) (hnp i)























theorem jc4_degenerate_orbitSplice (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hnp : ∀ i, bpc_NotProbed r ((dartNext K)^[i] a.1)) (hne : r ≠ a.1.tail)
    (hne' : (K \ {r}).Nonempty) :
    jc3_OrbitSpliceDatum K a r := by
  refine ⟨hne', ⟨a.1, jc4_basepoint_survives K a r hne⟩, 0, 0, dartOrbitPeriod K a, ?_, ?_, ?_, ?_⟩
  · 
    rw [Nat.zero_add]
  · 
    rw [Nat.zero_add]
    exact jc4_period_eq K a r hnp hne
  · 
    intro i _
    
    simp only [Nat.zero_add]
    exact ⟨jc4_iterate_coincide K a r hnp i, hnp i⟩
  · 
    rw [jc_windowTurn_eq, jc_windowTurn_eq, umEar_windowTurn_self, umEar_windowTurn_self]














theorem jc4_footprintDisjoint_of_not_footprint (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2) (hr : r ∉ bpc_orbitFootprint K a) :
    (∀ i, bpc_NotProbed r ((dartNext K)^[i] a.1)) ∧ r ≠ a.1.tail :=
  ⟨bpc_notProbed_of_not_footprint K a r hr, bpc_ne_tail_of_not_footprint K a r hr⟩






theorem jc4_not_saturating_of_footprintDisjoint (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hsat : ¬ K ⊆ bpc_orbitFootprint K a) :
    ∃ r, r ∈ K ∧ (∀ i, bpc_NotProbed r ((dartNext K)^[i] a.1)) ∧ r ≠ a.1.tail := by
  rw [Set.not_subset] at hsat
  obtain ⟨r, hrK, hr⟩ := hsat
  exact ⟨r, hrK, bpc_notProbed_of_not_footprint K a r hr, bpc_ne_tail_of_not_footprint K a r hr⟩












theorem jc4_footprintDisjoint_iff_not_footprint (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2) :
    r ∉ bpc_orbitFootprint K a ↔
      (∀ i, bpc_NotProbed r ((dartNext K)^[i] a.1)) ∧
        (∀ i, r ≠ ((dartNext K)^[i] a.1).tail) := by
  constructor
  · intro hr
    refine ⟨bpc_notProbed_of_not_footprint K a r hr, ?_⟩
    intro i heq
    exact hr ⟨i, Or.inr (Or.inr heq)⟩
  · rintro ⟨hnp, htail⟩ hmem
    obtain ⟨i, hi⟩ := hmem
    rcases hi with hi | hi | hi
    · exact (hnp i).1 hi.symm
    · exact (hnp i).2 hi.symm
    · exact htail i hi



















theorem jc4_cornerBalance_coincide (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (hnp : ∀ i, bpc_NotProbed r ((dartNext K)^[i] a.1)) (hne : r ≠ a.1.tail) :
    cornerBalance (K \ {r}) ⟨a.1, jc4_basepoint_survives K a r hne⟩ = cornerBalance K a :=
  bpc_cornerBalance_diff_singleton K r a ⟨a.1, jc4_basepoint_survives K a r hne⟩ rfl hnp













theorem jc4_farCell_coincide (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (hr : r ∉ bpc_orbitFootprint K a) (k : ℕ) :
    (dartNext (K \ {r}))^[k] a.1 = (dartNext K)^[k] a.1 :=
  jc4_iterate_coincide K a r (bpc_notProbed_of_not_footprint K a r hr) k






theorem jc4_farCell_degenerate_orbitSplice (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2) (hr : r ∉ bpc_orbitFootprint K a)
    (hne' : (K \ {r}).Nonempty) :
    jc3_OrbitSpliceDatum K a r :=
  jc4_degenerate_orbitSplice K a r (bpc_notProbed_of_not_footprint K a r hr)
    (bpc_ne_tail_of_not_footprint K a r hr) hne'








































end Walls

end StatMech

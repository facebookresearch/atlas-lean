/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Mathlib
import Code.Walls.jc2_engine
import Code.Walls.jc3_core
import Code.Lattice.BalancePreservingContraction

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice
























theorem jc4_tail_turn (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (a' : {e : Dart // IsBoundaryDart (K \ {r}) e}) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] a.1) =
        turnZ (K \ {r}) ((dartNext (K \ {r}))^[m' + i] a'.1)) :
    jc_windowTurn K a.1 m (m + n) = jc_windowTurn (K \ {r}) a'.1 m' (m' + n) :=
  jc2_tail_turn_eq K (K \ {r}) a.1 a'.1 m m' n hmatch





























theorem jc4_tail_turn_of_dartLockstep (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (a' : {e : Dart // IsBoundaryDart (K \ {r}) e}) (m m' n : ℕ)
    (htail : ∀ i, i < n →
      (dartNext (K \ {r}))^[m' + i] a'.1 = (dartNext K)^[m + i] a.1 ∧
      bpc_NotProbed r ((dartNext K)^[m + i] a.1)) :
    jc_windowTurn K a.1 m (m + n) = jc_windowTurn (K \ {r}) a'.1 m' (m' + n) := by
  apply jc4_tail_turn
  intro i hi
  obtain ⟨heq, hnp⟩ := htail i hi
  
  rw [heq]
  
  exact (bpc_turnZ_diff_singleton K r ((dartNext K)^[m + i] a.1) hnp).symm














theorem jc4_orbitSpliceDatum_tail_turn (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (h : jc3_OrbitSpliceDatum K a r) :
    ∃ (_ : (K \ {r}).Nonempty) (a' : {e : Dart // IsBoundaryDart (K \ {r}) e}) (m m' n : ℕ),
      dartOrbitPeriod K a = m + n ∧
      dartOrbitPeriod (K \ {r}) a' = m' + n ∧
      jc_windowTurn K a.1 m (m + n) = jc_windowTurn (K \ {r}) a'.1 m' (m' + n) := by
  obtain ⟨hne', a', m, m', n, hp, hp', htail, _hbal⟩ := h
  exact ⟨hne', a', m, m', n, hp, hp', jc4_tail_turn_of_dartLockstep K a r a' m m' n htail⟩











theorem jc4_tail_turn_general (K K' : Set (Site 2)) (e e' : Dart) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e')) :
    jc_windowTurn K e m (m + n) = jc_windowTurn K' e' m' (m' + n) :=
  jc2_tail_turn_eq K K' e e' m m' n hmatch





theorem jc4_tail_turn_general_eq_engine (K K' : Set (Site 2)) (e e' : Dart) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e')) :
    jc4_tail_turn_general K K' e e' m m' n hmatch =
      jc2_tail_turn_eq K K' e e' m m' n hmatch := rfl









theorem jc4_tail_turn_empty (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (a' : {e : Dart // IsBoundaryDart (K \ {r}) e}) (m m' : ℕ) :
    jc_windowTurn K a.1 m (m + 0) = jc_windowTurn (K \ {r}) a'.1 m' (m' + 0) :=
  jc4_tail_turn K a r a' m m' 0 (by intro i hi; omega)





theorem jc4_tail_turn_self (K : Set (Site 2)) (e : Dart) (m n : ℕ) :
    jc_windowTurn K e m (m + n) = jc_windowTurn K e m (m + n) :=
  jc4_tail_turn_general K K e e m m n (by intro i hi; rfl)




theorem jc4_tail_turn_of_dartLockstep_empty (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (a' : {e : Dart // IsBoundaryDart (K \ {r}) e}) (m m' : ℕ) :
    jc_windowTurn K a.1 m (m + 0) = jc_windowTurn (K \ {r}) a'.1 m' (m' + 0) :=
  jc4_tail_turn_of_dartLockstep K a r a' m m' 0 (by intro i hi; omega)

































end Walls

end StatMech

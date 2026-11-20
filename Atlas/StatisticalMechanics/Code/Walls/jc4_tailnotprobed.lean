/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Mathlib
import Code.Walls.jc3_earfootprint
import Code.Walls.jc3_core
import Code.Lattice.BalancePreservingContraction

open SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice























def jc4_TailFootprintFree (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (m n : ℕ) : Prop :=
  ∀ i, i < n → jc3_AvoidsEarFootprint r ((dartNext K)^[m + i] a.1)














theorem jc4_tnp_footprintAgree (r : Site 2) (e : Dart) (h : jc3_AvoidsEarFootprint r e) :
    bpc_NotProbed r e :=
  jc3_notProbed_of_avoidsEarFootprint r e h











theorem jc4_tail_notProbed_single (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (m i : ℕ) (h : jc3_AvoidsEarFootprint r ((dartNext K)^[m + i] a.1)) :
    bpc_NotProbed r ((dartNext K)^[m + i] a.1) :=
  jc4_tnp_footprintAgree r _ h

















theorem jc4_tail_notProbed (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (m n : ℕ) (h : jc4_TailFootprintFree K a r m n) :
    ∀ i, i < n → bpc_NotProbed r ((dartNext K)^[m + i] a.1) := by
  intro i hi
  exact jc4_tail_notProbed_single K a r m i (h i hi)










theorem jc4_tailFootprintFree_of_vacuous (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2) (m : ℕ) :
    jc4_TailFootprintFree K a r m 0 := by
  intro i hi
  exact absurd hi (Nat.not_lt_zero i)
















theorem jc4_farTail_footprintFree (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (m n : ℕ)
    (hconst : ∀ i, i < n → (dartNext K)^[m + i] a.1 = jc3_farDart) :
    jc4_TailFootprintFree K a (![0, 0] : Site 2) m n := by
  intro i hi
  rw [hconst i hi]
  exact jc3_farDart_avoidsOrigin





theorem jc4_farTail_notProbed (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (m n : ℕ)
    (hconst : ∀ i, i < n → (dartNext K)^[m + i] a.1 = jc3_farDart) :
    ∀ i, i < n → bpc_NotProbed (![0, 0] : Site 2) ((dartNext K)^[m + i] a.1) :=
  jc4_tail_notProbed K a (![0, 0] : Site 2) m n (jc4_farTail_footprintFree K a m n hconst)


















theorem jc4_spliceTailClause (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (a' : {e : Dart // IsBoundaryDart (K \ {r}) e}) (m m' n : ℕ)
    (heq : ∀ i, i < n →
      (dartNext (K \ {r}))^[m' + i] a'.1 = (dartNext K)^[m + i] a.1)
    (hconf : jc4_TailFootprintFree K a r m n) :
    ∀ i, i < n →
      (dartNext (K \ {r}))^[m' + i] a'.1 = (dartNext K)^[m + i] a.1 ∧
        bpc_NotProbed r ((dartNext K)^[m + i] a.1) := by
  intro i hi
  exact ⟨heq i hi, jc4_tail_notProbed K a r m n hconf i hi⟩






theorem jc4_orbitSpliceDatum_of_confined (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hne' : (K \ {r}).Nonempty) (a' : {e : Dart // IsBoundaryDart (K \ {r}) e})
    (m m' n : ℕ)
    (hp : dartOrbitPeriod K a = m + n)
    (hp' : dartOrbitPeriod (K \ {r}) a' = m' + n)
    (heq : ∀ i, i < n →
      (dartNext (K \ {r}))^[m' + i] a'.1 = (dartNext K)^[m + i] a.1)
    (hconf : jc4_TailFootprintFree K a r m n)
    (hbal : jc_windowTurn (K \ {r}) a'.1 0 m' = jc_windowTurn K a.1 0 m) :
    jc3_OrbitSpliceDatum K a r :=
  ⟨hne', a', m, m', n, hp, hp',
    jc4_spliceTailClause K a r a' m m' n heq hconf, hbal⟩






























end Walls

end StatMech

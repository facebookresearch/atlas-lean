/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































































import Mathlib
import Code.Walls.jc4_core
import Code.Walls.jc4_firstreturnK
import Code.Walls.jc4_tailnotprobed
import Code.Walls.jc5_firstreturn
import Code.Walls.jc5_singlecycle
import Code.Walls.jc5_earframe
import Code.Walls.jc5_footprintdartsfinite
import Code.Lattice.DartOrbit

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice























def jc5_NoReentry (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2) : Prop :=
  ∀ i, i < dartOrbitPeriod K a → ¬ jc4_FootprintFree K a r i →
    ∀ k, k ≤ i → ¬ jc4_FootprintFree K a r k









def jc5_TouchingConvex (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) : Prop :=
  ∀ i j k, i < j → j < k → ¬ jc4_FootprintFree K a r i → ¬ jc4_FootprintFree K a r k →
    ¬ jc4_FootprintFree K a r j























theorem jc5_tailFootprintFree_of_noReentry (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
    (hnore : jc5_NoReentry K a r) :
    jc4_TailFootprintFree K a r (jc4_firstReturnK K a r hex)
      (dartOrbitPeriod K a - jc4_firstReturnK K a r hex) := by
  intro i hi
  have hmi : jc4_firstReturnK K a r hex + i < dartOrbitPeriod K a := by omega
  exact jc4_firstReturnK_remains_free_of_initialBlock K a r hex hnore
    (jc4_firstReturnK K a r hex + i) (by omega) hmi






















theorem jc5_noReentry_of_convex (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (ha0 : ¬ jc4_FootprintFree K a r 0)
    (hconv : jc5_TouchingConvex K a r) :
    jc5_NoReentry K a r := by
  intro i _hi htouch k hk
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact ha0
  · rcases eq_or_lt_of_le hk with rfl | hlt
    · exact htouch
    · exact hconv 0 k i hkpos hlt ha0 htouch








theorem jc5_tailFootprintFree_of_convex (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
    (ha0 : ¬ jc4_FootprintFree K a r 0)
    (hconv : jc5_TouchingConvex K a r) :
    jc4_TailFootprintFree K a r (jc4_firstReturnK K a r hex)
      (dartOrbitPeriod K a - jc4_firstReturnK K a r hex) :=
  jc5_tailFootprintFree_of_noReentry K a r hex (jc5_noReentry_of_convex K a r ha0 hconv)
















theorem jc5_period_decomp (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
    (hle : jc4_firstReturnK K a r hex ≤ dartOrbitPeriod K a) :
    dartOrbitPeriod K a =
      jc4_firstReturnK K a r hex + (dartOrbitPeriod K a - jc4_firstReturnK K a r hex) := by
  omega

























theorem jc5_orbitSpliceDatum_of_noReentry (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
    (hnore : jc5_NoReentry K a r)
    (hne' : (K \ {r}).Nonempty) (a' : {e : Dart // IsBoundaryDart (K \ {r}) e}) (m' : ℕ)
    (hp : dartOrbitPeriod K a =
      jc4_firstReturnK K a r hex + (dartOrbitPeriod K a - jc4_firstReturnK K a r hex))
    (hp' : dartOrbitPeriod (K \ {r}) a' =
      m' + (dartOrbitPeriod K a - jc4_firstReturnK K a r hex))
    (heq : ∀ i, i < dartOrbitPeriod K a - jc4_firstReturnK K a r hex →
      (dartNext (K \ {r}))^[m' + i] a'.1 =
        (dartNext K)^[jc4_firstReturnK K a r hex + i] a.1)
    (hbal : jc_windowTurn (K \ {r}) a'.1 0 m' =
      jc_windowTurn K a.1 0 (jc4_firstReturnK K a r hex)) :
    jc3_OrbitSpliceDatum K a r :=
  jc4_orbitSpliceDatum_of_confined K a r hne' a' (jc4_firstReturnK K a r hex) m'
    (dartOrbitPeriod K a - jc4_firstReturnK K a r hex) hp hp' heq
    (jc5_tailFootprintFree_of_noReentry K a r hex hnore) hbal














theorem jc5_noReentry_of_disjoint (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hfoot : ∀ i, jc4_FootprintFree K a r i) :
    jc5_NoReentry K a r := by
  intro i _ hi _ _
  exact absurd (hfoot i) hi





theorem jc5_touchingConvex_of_disjoint (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hfoot : ∀ i, jc4_FootprintFree K a r i) :
    jc5_TouchingConvex K a r := by
  intro i j k _ _ hi _
  exact absurd (hfoot i) hi






theorem jc5_noReentry_of_avoids (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hfoot : ∀ i, jc3_AvoidsEarFootprint r ((dartNext K)^[i] a.1)) :
    jc5_NoReentry K a r :=
  jc5_noReentry_of_disjoint K a r hfoot



















theorem jc5_orbit_isCycle (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    (dartOrbitWalk K a).IsCycle :=
  jc5_dartOrbitWalk_isCycle K hK a






theorem jc5_touchingDarts_finite (r : Site 2) :
    {e : Dart | jc5_ProbesEarFootprint r e}.Finite :=
  jc5_footprintDarts_finite r






theorem jc5_firstReturn_landmark (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
    (ha0 : ¬ jc4_FootprintFree K a r 0) :
    (1 ≤ jc4_firstReturnK K a r hex ∧
        jc4_FootprintFree K a r (jc4_firstReturnK K a r hex) ∧
        (∀ k, 1 ≤ k → jc4_FootprintFree K a r k → jc4_firstReturnK K a r hex ≤ k)) ∧
      (∀ k, k < jc4_firstReturnK K a r hex → ¬ jc4_FootprintFree K a r k) :=
  jc5_firstReturn K a r hex ha0














def jc5_ExcursionConfined (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i) : Prop :=
  jc4_TailFootprintFree K a r (jc4_firstReturnK K a r hex)
    (dartOrbitPeriod K a - jc4_firstReturnK K a r hex)






theorem jc5_excursionConfined_of_noReentry (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
    (hnore : jc5_NoReentry K a r) :
    jc5_ExcursionConfined K a r hex :=
  jc5_tailFootprintFree_of_noReentry K a r hex hnore





theorem jc5_excursionConfined_of_convex (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
    (ha0 : ¬ jc4_FootprintFree K a r 0)
    (hconv : jc5_TouchingConvex K a r) :
    jc5_ExcursionConfined K a r hex :=
  jc5_tailFootprintFree_of_convex K a r hex ha0 hconv






















































end Walls

end StatMech

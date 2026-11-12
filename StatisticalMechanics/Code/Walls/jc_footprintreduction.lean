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
import Code.Lattice.TurningNumber
import Code.Lattice.CornerBalance
import Code.Lattice.EarContraction
import Code.Lattice.BalanceContraction
import Code.Lattice.GaussBonnetEar
import Code.Lattice.BalancePreservingContraction

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice













abbrev jc_NotProbed (c : Site 2) (e : Dart) : Prop := bpc_NotProbed c e




abbrev jc_orbitFootprint (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    Set (Site 2) := bpc_orbitFootprint K a







abbrev jc_BalanceSaturatingContraction : Prop := bpc_BalanceSaturatingContraction


















theorem jc_orbit_unchanged_of_not_footprint (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (c : Site 2)
    (hc : c ∉ jc_orbitFootprint K a) (k : ℕ) :
    (dartNext (K \ {c}))^[k] a.1 = (dartNext K)^[k] a.1 :=
  bpc_iterate_dartNext_diff_singleton K c a.1
    (bpc_notProbed_of_not_footprint K a c hc) k



















theorem jc_cornerBalance_unchanged_of_not_footprint (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (c : Site 2)
    (hc : c ∉ jc_orbitFootprint K a)
    (hbd : IsBoundaryDart (K \ {c}) a.1) :
    cornerBalance (K \ {c}) ⟨a.1, hbd⟩ = cornerBalance K a :=
  bpc_cornerBalance_diff_singleton K c a ⟨a.1, hbd⟩ rfl
    (bpc_notProbed_of_not_footprint K a c hc)












theorem jc_contraction_of_not_saturating (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (c : Site 2) (hcK : c ∈ K)
    (hc : c ∉ jc_orbitFootprint K a) :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a :=
  bpc_contraction_of_not_saturating K hK a c hcK hc
















theorem jc_footprintReduction (h : jc_BalanceSaturatingContraction) :
    BalancePreservingContraction :=
  bpc_balancePreservingContraction_of_saturating h







theorem jc_footprintReduction_iff :
    BalancePreservingContraction ↔ jc_BalanceSaturatingContraction := by
  constructor
  · intro h K hK hge a _
    exact h K hK hge a
  · exact jc_footprintReduction












theorem jc_totalTurn_eq_four_of_saturating (K : Set (Site 2))
    (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hsat : jc_BalanceSaturatingContraction) :
    TurningIsFullRevolution (ndt_StarHull K) a :=
  gbe_totalTurn_eq_four_of_contraction K hSK hne a (jc_footprintReduction hsat)




theorem jc_totalTurn_eq_four_value_of_saturating (K : Set (Site 2))
    (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hsat : jc_BalanceSaturatingContraction) :
    totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
      totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 :=
  jc_totalTurn_eq_four_of_saturating K hSK hne a hsat















theorem jc_domino_saturating_witness :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < domino.ncard ∧ cornerBalance K' a' = cornerBalance domino dmBase :=
  bpc_domino_balanceSaturatingContraction_witness






























end Walls

end StatMech

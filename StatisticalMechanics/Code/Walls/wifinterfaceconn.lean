/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Mathlib
import Code.Walls.wpbpivotbridge
import Code.Lattice.InterfaceConnected
import Code.Lattice.InterfaceConnectedProof
import Code.Lattice.InterfaceConnectedGlobal
import Code.Lattice.FacialSurjectivity
import Code.Lattice.KingFacts

open SimpleGraph Function

namespace StatMech

namespace Wif

open StatMech.Lattice
open StatMech.Wpb
open StatMech.Wcd
open StatMech.Walls
open StatMech.Euc











theorem wif_orbitCovers_of_interfaceConnected (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hIC : InterfaceConnected K)
    (hheads : ∀ d : Dart, (hd : IsBoundaryDart K d) →
      ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨a.1.head, a.2.2⟩ ⟨d.head, hd.2⟩) :
    WpbOrbitCovers K a :=
  fsv_hsat_of_interfaceConnected K hIC a.2 hheads















theorem wif_interfaceConnected_of_orbitCovers (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (hcov : WpbOrbitCovers K a) :
    InterfaceConnected K := by
  intro e f he hf _hreach
  have hae : SameOrbit K a.1 e := hcov e he
  have haf : SameOrbit K a.1 f := hcov f hf
  exact SameOrbit.trans (SameOrbit.symm_of_finite hK a.2 hae) haf











theorem wif_revCount_pm_one (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e})
    (hpf : WpbPinchFree K a) (hIC : InterfaceConnected K)
    (hheads : ∀ d : Dart, (hd : IsBoundaryDart K d) →
      ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨a.1.head, a.2.2⟩ ⟨d.head, hd.2⟩)
    (hbuild : Euc.EucBuildable (wcd_toVtxFinset K hK)) :
    revCount K a = 1 ∨ revCount K a = -1 :=
  wpb_revCount_pm_one K hK a hpf (wif_orbitCovers_of_interfaceConnected K a hIC hheads) hbuild



theorem wif_balanceIsFour (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e})
    (hpf : WpbPinchFree K a) (hIC : InterfaceConnected K)
    (hheads : ∀ d : Dart, (hd : IsBoundaryDart K d) →
      ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨a.1.head, a.2.2⟩ ⟨d.head, hd.2⟩)
    (hbuild : Euc.EucBuildable (wcd_toVtxFinset K hK)) :
    BalanceIsFour K a :=
  wpb_balanceIsFour K hK a hpf (wif_orbitCovers_of_interfaceConnected K a hIC hheads) hbuild









theorem wif_boundaryKingConnected (K : Set (Site 2)) : BoundaryKingConnected K :=
  kf_boundaryKingConnected K











theorem wif_kingTransport_route_dead :
    ¬ OrbitKingTransport ({(0 : Site 2)} : Set (Site 2)) :=
  ifg_not_orbitKingTransport_singleton




theorem wif_interfaceConnected_iff_orbitTraceSurjective (K : Set (Site 2)) :
    InterfaceConnected K ↔ OrbitTraceSurjective K :=
  (orbitTraceSurjective_iff_interfaceConnected K).symm










theorem wif_interfaceConnected_unitCell : InterfaceConnected unitCell := by
  show InterfaceConnected ({(![0, 0] : Site 2)} : Set (Site 2))
  exact ifc_interfaceConnected (![0, 0])






theorem wif_interfaceConnected_unitCell_of_orbitCovers : InterfaceConnected unitCell :=
  wif_interfaceConnected_of_orbitCovers unitCell wcd_unitCell_finite ucBase
    wpb_witness_orbitCovers_unitCell

end Wif

end StatMech

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingSurfaceTensionFiniteVolume
import Code.Ising.PlusStateSpinProfileLimit

open MeasureTheory Filter Topology

namespace StatMech.Ising

open StatMech.Lattice

noncomputable section

variable {d : Nat}


def interfaceMeasure (i : Fin d) (n : Nat) (beta : Real) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  fvProbabilityMeasure (interfaceField i) n (bondFinsetTouch d n) beta 0


def interfaceState (i : Fin d) (beta : Real) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  limitState (fun n => interfaceMeasure i n beta)

theorem interfaceState_isInfiniteVolumeState (i : Fin d) (beta : Real) :
    InfiniteVolumeState (fun n => interfaceMeasure i n beta)
      (interfaceState i beta) :=
  limitState_isInfiniteVolumeState _




theorem exists_interfaceMeasure_spin_profile_tendsto
    (i : Fin d) (beta : Real) :
    ∃ phi : Nat -> Nat, StrictMono phi ∧ forall x : Site d,
      Tendsto
        (fun n => ∫ omega, spin omega x
          ∂(interfaceMeasure i (phi n) beta :
            Measure (ConfigSpace (Site d))))
        atTop
        (nhds (∫ omega, spin omega x
          ∂(interfaceState i beta : Measure (ConfigSpace (Site d))))) := by
  obtain ⟨phi, hphi, hconv⟩ := interfaceState_isInfiniteVolumeState i beta
  refine ⟨phi, hphi, ?_⟩
  intro x
  have hlim := hconv.tendsto_integral (spinBCF x)
  simpa only [Function.comp_apply, spinBCF_apply] using hlim



theorem exists_common_plus_interface_spin_profile_tendsto
    (i : Fin d) (beta : Real) (hbeta : 0 <= beta) :
    ∃ phi : Nat -> Nat, StrictMono phi ∧ forall x : Site d,
      (Tendsto
        (fun n => ∫ omega, spin omega x
          ∂(plusMeasure d (phi n) beta 0 :
            Measure (ConfigSpace (Site d))))
        atTop (nhds (magnetization d beta))) ∧
      (Tendsto
        (fun n => ∫ omega, spin omega x
          ∂(interfaceMeasure i (phi n) beta :
            Measure (ConfigSpace (Site d))))
        atTop
        (nhds (∫ omega, spin omega x
          ∂(interfaceState i beta : Measure (ConfigSpace (Site d)))))) := by
  obtain ⟨phi, hphi, hinterface⟩ :=
    exists_interfaceMeasure_spin_profile_tendsto i beta
  refine ⟨phi, hphi, ?_⟩
  intro x
  exact ⟨(plusMeasure_spin_full_tendsto_magnetization beta hbeta x).comp
      hphi.tendsto_atTop,
    hinterface x⟩

end

end StatMech.Ising

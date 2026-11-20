/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.EarExistence
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.JordanExteriorClosure
import Code.Walls.jc11core

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice
















theorem kc6_windingWitness (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ c : Site 2, ∃ hc : IsExtremeCell K c,
      c ∈ K ∧ ¬ Even (jec_rayCount c (mpl_orbitLoop K (extremeBase K c hc))) := by
  obtain ⟨c, hc⟩ := exists_extremeCell K hK hne
  exact ⟨c, hc, hc.mem, jc11_cornerCellOdd K hK c hc⟩









theorem kc6_exists_windingWitness_dart (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ a : {e : Dart // IsBoundaryDart K e}, ∃ z₀ : Site 2,
      z₀ ∈ K ∧ ¬ Even (jec_rayCount z₀ (mpl_orbitLoop K a)) := by
  obtain ⟨c, hc, hcmem, hodd⟩ := kc6_windingWitness K hK hne
  exact ⟨extremeBase K c hc, c, hcmem, hodd⟩






theorem kc6_windingWitness_mem_leftRegion (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ c : Site 2, ∃ hc : IsExtremeCell K c,
      c ∈ K ∧ c ∈ jec_leftRegion (mpl_orbitLoop K (extremeBase K c hc)) := by
  obtain ⟨c, hc, hcmem, hodd⟩ := kc6_windingWitness K hK hne
  exact ⟨c, hc, hcmem, (jec_mem_leftRegion _ c).mpr hodd⟩












theorem kc6_unitCell_windingWitness :
    (![0, 0] : Site 2) ∈ unitCell ∧
      ¬ Even (jec_rayCount (![0, 0] : Site 2) (mpl_orbitLoop unitCell ucBase)) := by
  refine ⟨?_, ?_⟩
  · rw [unitCell, Set.mem_singleton_iff]
  · rw [mpl_unitCell_rayCount_eq_one]
    decide

end Walls

end StatMech

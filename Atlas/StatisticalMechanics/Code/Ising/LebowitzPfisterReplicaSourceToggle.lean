/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaSeamCrossing
import Code.FrontierA.GrahamGeneralSourceSwitching










open Finset
open scoped symmDiff

namespace StatMech.Ising

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.FrontierA

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _

local instance (G : SimpleGraph V) (sites : I -> V)
    (u v : LPReplicaCurrentVertex V) :
    DecidablePred (fun n : Current (LPReplicaCurrentVertex V) =>
      CurrentConnected (lpReplicaCurrentGraph G sites) n u v) :=
  fun _ => Classical.propDecidable _

theorem lpReplicaCurrent_left_ne_right
    (sites : I -> V) (i : I) :
    lpReplicaCurrentLeft sites i ≠ lpReplicaCurrentRight sites i := by
  simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]


theorem lpReplicaCurrent_pair_eq_seamSource
    (sites : I -> V) (i : I) :
    ({lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i} :
        Finset (LPReplicaCurrentVertex V)) =
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i := by
  ext z
  unfold lpMatchingSeamSource
  simp only [Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_symmDiff]
  have hne := lpReplicaCurrent_left_ne_right sites i
  constructor
  · rintro (hz | hz)
    · exact Or.inl ⟨hz, fun hr => hne (hz.symm.trans hr)⟩
    · exact Or.inr ⟨hz, fun hl => hne (hl.symm.trans hz)⟩
  · rintro (⟨hz, _⟩ | ⟨hz, _⟩)
    · exact Or.inl hz
    · exact Or.inr hz




theorem lpReplica_gatedSourcePairSum_toggle_seam
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 (LPReplicaCurrentVertex V) -> Real)
    (A B : Finset (LPReplicaCurrentVertex V)) (i : I)
    (P : Current (LPReplicaCurrentVertex V) -> Prop) [DecidablePred P] :
    gatedSourcePairSum (lpReplicaCurrentGraph G sites) beta J A B
        (fun n => P n ∧ CurrentConnected (lpReplicaCurrentGraph G sites) n
          (lpReplicaCurrentLeft sites i) (lpReplicaCurrentRight sites i)) =
      gatedSourcePairSum (lpReplicaCurrentGraph G sites) beta J
        (A ∆ lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
        (B ∆ lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
        (fun n => P n ∧ CurrentConnected (lpReplicaCurrentGraph G sites) n
          (lpReplicaCurrentLeft sites i) (lpReplicaCurrentRight sites i)) := by
  have h := gatedSourcePairSum_shift_connected
    (lpReplicaCurrentGraph G sites) beta J A B
    (lpReplicaCurrent_left_ne_right sites i) P
  simpa only [lpReplicaCurrent_pair_eq_seamSource] using h




theorem lpReplica_gatedDisconn_toggle_seam
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 (LPReplicaCurrentVertex V) -> Real)
    (A B : Finset (LPReplicaCurrentVertex V)) (i : I) :
    gatedSourcePairSum (lpReplicaCurrentGraph G sites) beta J A B
        (fun n =>
          ¬ CurrentConnected (lpReplicaCurrentGraph G sites) n
              lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 ∧
          CurrentConnected (lpReplicaCurrentGraph G sites) n
              (lpReplicaCurrentLeft sites i)
              (lpReplicaCurrentRight sites i)) =
      gatedSourcePairSum (lpReplicaCurrentGraph G sites) beta J
        (A ∆ lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
        (B ∆ lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
        (fun n =>
          ¬ CurrentConnected (lpReplicaCurrentGraph G sites) n
              lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 ∧
          CurrentConnected (lpReplicaCurrentGraph G sites) n
              (lpReplicaCurrentLeft sites i)
              (lpReplicaCurrentRight sites i)) := by
  exact lpReplica_gatedSourcePairSum_toggle_seam G sites beta J A B i
    (fun n => ¬ CurrentConnected (lpReplicaCurrentGraph G sites) n
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)

end

end StatMech.Ising

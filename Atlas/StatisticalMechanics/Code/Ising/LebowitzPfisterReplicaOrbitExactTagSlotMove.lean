/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitExactTagProjection
import Code.Ising.LebowitzPfisterReplicaOrbitRankFour

open Finset
open scoped symmDiff

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj := Classical.decRel _


theorem lpReplicaOrbitCommonSlotsOfCopies_injective
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    Function.Injective
      (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L) := by
  exact Finset.map_injective
    (lpReplicaProfileCopyEquivCommonSlot G sites q m hm L).toEmbedding


theorem lpReplicaOrbitFourColorSlotRowMask_stateOfTag
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag) =
      lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L
        (lpReplicaRowCopies G sites m tag true) := by
  ext x
  rw [mem_lpReplicaOrbitCommonSlotsOfCopies_iff]
  simp only [lpReplicaOrbitFourColorSlotRowMask,
    lpReplicaOrbitFourColorSlotStateOfTag, lpReplicaRowCopies,
    Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.symm_apply_apply]


theorem lpReplicaOrbitFourColorSlotCrossToggle_left_injective
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    Function.Injective fun P =>
      lpReplicaOrbitFourColorSlotCrossToggle G sites q P s := by
  intro P Q h
  have hrow := congrArg
    (lpReplicaOrbitFourColorSlotRowMask G sites q) h
  rw [lpReplicaOrbitFourColorSlotRowMask_crossToggle,
    lpReplicaOrbitFourColorSlotRowMask_crossToggle] at hrow
  exact symmDiff_right_injective
    (lpReplicaOrbitFourColorSlotRowMask G sites q s) hrow


theorem lpReplicaOrbitFourColorSlotEdge_crossToggle_of_not_mem
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q)
    (x : LPReplicaOrbitCommonSlot G sites q) (hx : x ∉ P) :
    lpReplicaOrbitFourColorSlotEdge G sites q
        (lpReplicaOrbitFourColorSlotCrossToggle G sites q P s) x =
      lpReplicaOrbitFourColorSlotEdge G sites q s x := by
  rcases x with fixed | ⟨strict, k⟩
  · rfl
  · change lpReplicaOrbitFourColorSlotEdge G sites q
      (lpReplicaOrbitFourColorSlotReflect G sites q P s)
        (Sum.inr ⟨strict, k⟩) = _
    rw [lpReplicaOrbitFourColorSlotEdge_reflect_strict]
    exact if_neg hx


theorem lpReplicaOrbitFourColorSlotEdge_crossToggle_of_mem
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q)
    (x : LPReplicaOrbitCommonSlot G sites q) (hx : x ∈ P) :
    lpReplicaOrbitFourColorSlotEdge G sites q
        (lpReplicaOrbitFourColorSlotCrossToggle G sites q P s) x =
      lpReplicaCurrentEdgeReflect G sites
        (lpReplicaOrbitFourColorSlotEdge G sites q s x) := by
  rcases x with fixed | ⟨strict, k⟩
  · change fixed.1.1 = lpReplicaCurrentEdgeReflect G sites fixed.1.1
    exact (mem_lpReplicaCurrentEdgeOrbitFixed G sites fixed.1.1).mp fixed.1.2
  · change lpReplicaOrbitFourColorSlotEdge G sites q
      (lpReplicaOrbitFourColorSlotReflect G sites q P s)
        (Sum.inr ⟨strict, k⟩) = _
    rw [lpReplicaOrbitFourColorSlotEdge_reflect_strict]
    exact if_pos hx



theorem lpReplicaOffdiagDecoratedTarget_ne_of_singletonCrossToggle
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (y w : LPReplicaOffdiagDecoratedTarget G sites i j q)
    (c e : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hy : (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q y).2 =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
          z.1.1.2 z.2.2 {c})
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z))
    (hw : (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q w).2 =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
          z.1.1.2 z.2.2 {e})
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z))
    (hce : c ≠ e) : y ≠ w := by
  intro hyw
  have hcross : lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
          z.1.1.2 z.2.2 {c})
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
          z.1.1.2 z.2.2 {e})
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
    rw [← hy, ← hw, hyw]
  have hmask := lpReplicaOrbitFourColorSlotCrossToggle_left_injective
    G sites q (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)
      hcross
  have hcopies := lpReplicaOrbitCommonSlotsOfCopies_injective
    G sites q z.1.1.1 z.1.1.2 z.2.2 hmask
  exact hce (Finset.singleton_injective hcopies)

set_option maxHeartbeats 400000 in



theorem lpReplicaBalancedSelector_slotState_of_singletonToggle
    (G : SimpleGraph V) (sites : I -> V)
    (Si Sj T : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaBalancedSelector G sites
      (Si ∆ Sj ∆ T) (Sj ∆ T) q)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) s.profile)
    (sourceTag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) s.profile -> LPReplicaRowTag)
    (hmove : lpReplicaToggleRows G sites s.profile s.selector s.tag =
      lpReplicaToggleRows G sites s.profile {c} sourceTag)
    (hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites) :
    lpReplicaOrientedFourColorSlotState G sites Si
        ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites Si
          ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) q
          (lpReplicaDecoratedOrbitAtomOfBalancedSelector
            G sites Si Sj T q s)) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q s.profile s.orbit
          s.orbitLabel {c})
        (lpReplicaOrbitFourColorSlotStateOfTag G sites q s.profile s.orbit
          s.orbitLabel sourceTag) := by
  classical
  let moved := lpReplicaToggleRows G sites s.profile s.selector s.tag
  let atom := lpReplicaDecoratedOrbitAtomOfBalancedSelector
    G sites Si Sj T q s
  let oz := lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites Si
    ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) q atom
  let targetTag := lpReplicaOrientedFourColorTag G sites Si
    ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) q oz
  have htag : targetTag = moved := by
    change lpReplicaOrientedFourColorTag G sites Si
      ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) q
      (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites Si
        ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) q
        (lpReplicaDecoratedOrbitAtomOfBalancedSelector
          G sites Si Sj T q s)) = moved
    unfold lpReplicaDecoratedOrbitAtomOfBalancedSelector
    apply lpReplicaOrientedFourColorTag_ofRowGate
  change lpReplicaOrbitFourColorSlotStateOfTag G sites q s.profile s.orbit
      s.orbitLabel targetTag = _
  rw [lpReplicaOrbitFourColorSlotCrossToggle,
    lpReplicaOrbitFourColorSlotReflect_singletonCopy_of_fixed
      G sites q s.profile s.orbit s.orbitLabel c hfixed,
    lpReplicaOrbitFourColorSlotRowToggle_stateOfTag, htag]
  simpa only [moved] using congrArg
    (lpReplicaOrbitFourColorSlotStateOfTag
      G sites q s.profile s.orbit s.orbitLabel) hmove

end
end StatMech.Ising

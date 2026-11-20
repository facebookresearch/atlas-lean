/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.PermOrbitWeightSum
import Code.FrontierD.FKRectRefinedIntersection



open Equiv Finset

namespace StatMech.FrontierD

noncomputable section



theorem fkMedialCheckerColor_localMate_eq_not
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d : FKMedialDart T) :
    fkMedialCheckerColor (fkMedialLocalMate pairing d) =
      !fkMedialCheckerColor d := by
  have hne := fkMedialCheckerColor_localMate_ne pairing d
  generalize hd : fkMedialCheckerColor d = b at hne ⊢
  generalize hm : fkMedialCheckerColor
    (fkMedialLocalMate pairing d) = c at hne ⊢
  cases b <;> cases c <;> simp_all



theorem fkMedial_reachable_localMate
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d : FKMedialDart T) :
    (fkMedialLoopGraph T pairing).Reachable d
      (fkMedialLocalMate pairing d) := by
  apply SimpleGraph.Adj.reachable
  rw [fkMedialLoopGraph_adj_iff]
  exact Or.inl rfl



theorem fkMedialBoundaryStep_localMate_conj
    {T : EvenTorus} (pairing : FKMedialLoopPairing T) :
    fkMedialLocalMateEquiv pairing * fkMedialBoundaryStep pairing *
        (fkMedialLocalMateEquiv pairing)⁻¹ =
      (fkMedialBoundaryStep pairing)⁻¹ := by
  apply Equiv.ext
  intro d
  simp [fkMedialBoundaryStep, fkMedialLocalMateEquiv,
    fkMedialBondMateEquiv, fkMedialLocalMate_involutive]



theorem fkMedialBoundaryStep_sameCycle_localMate_iff
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d e : FKMedialDart T) :
    (fkMedialBoundaryStep pairing).SameCycle
        (fkMedialLocalMate pairing d)
        (fkMedialLocalMate pairing e) ↔
      (fkMedialBoundaryStep pairing).SameCycle d e := by
  let tau := fkMedialLocalMateEquiv pairing
  let sigma := fkMedialBoundaryStep pairing
  have hconj : tau * sigma * tau⁻¹ = sigma⁻¹ :=
    fkMedialBoundaryStep_localMate_conj pairing
  have h := Equiv.Perm.sameCycle_conj
    (f := sigma) (g := tau) (x := tau d) (y := tau e)
  rw [hconj, Equiv.Perm.sameCycle_inv] at h
  simpa [tau, fkMedialLocalMateEquiv,
    fkMedialLocalMate_involutive] using h



theorem fkRectMedialBoundaryPrimalSeamIncrement_localMate
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) :
    fkRectMedialBoundaryPrimalSeamIncrement R pairing
        (fkMedialLocalMate pairing d) =
      -fkRectMedialBoundaryPrimalSeamIncrement R pairing d := by
  have hstart : fkRectMedialDartPrimalLabel R
        (fkMedialLocalMate pairing d) =
      fkRectMedialDartPrimalLabel R
        (fkMedialBoundaryStep pairing d) := by
    rw [fkMedialBoundaryStep_apply,
      fkRectMedialDartPrimalLabel_bondMate]
  have hend : fkRectMedialDartPrimalLabel R
        (fkMedialBoundaryStep pairing
          (fkMedialLocalMate pairing d)) =
      fkRectMedialDartPrimalLabel R d := by
    rw [fkMedialBoundaryStep_apply,
      fkMedialLocalMate_involutive,
      fkRectMedialDartPrimalLabel_bondMate]
  unfold fkRectMedialBoundaryPrimalSeamIncrement
  simp only [hstart, hend]
  apply Prod.ext
  · simp only [Prod.fst_neg]
    exact fkRectHorizontalSeamIncrement_swap R _ _
  · simp only [Prod.snd_neg]
    exact fkRectVerticalSeamIncrement_swap R _ _



def fkRectBoundaryCycleClassWinding
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) : Int × Int :=
  permCycleClassWeightSum (fkMedialBoundaryStep pairing) d
    (fkRectMedialBoundaryPrimalSeamIncrement R pairing)



theorem fkRectBoundaryCycleClassWinding_localMate
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) :
    fkRectBoundaryCycleClassWinding R pairing
        (fkMedialLocalMate pairing d) =
      -fkRectBoundaryCycleClassWinding R pairing d := by
  let sigma := fkMedialBoundaryStep pairing
  let tau := fkMedialLocalMateEquiv pairing
  let weight := fkRectMedialBoundaryPrimalSeamIncrement R pairing
  unfold fkRectBoundaryCycleClassWinding permCycleClassWeightSum
  calc
    (∑ x, if sigma.SameCycle (tau d) x then weight x else 0) =
        ∑ x, if sigma.SameCycle (tau d) (tau x) then
          weight (tau x) else 0 := by
      exact (tau.sum_comp
        (fun x => if sigma.SameCycle (tau d) x then weight x else 0)).symm
    _ = ∑ x, -(if sigma.SameCycle d x then weight x else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hcycle := fkMedialBoundaryStep_sameCycle_localMate_iff
        pairing d x
      have hweight := fkRectMedialBoundaryPrimalSeamIncrement_localMate
        R pairing x
      change (if sigma.SameCycle (tau d) (tau x) then
          weight (tau x) else 0) = _
      change sigma.SameCycle (tau d) (tau x) ↔
        sigma.SameCycle d x at hcycle
      change weight (tau x) = -weight x at hweight
      by_cases h : sigma.SameCycle d x
      · rw [if_pos h, if_pos (hcycle.mpr h), hweight]
      · rw [if_neg h, if_neg (mt hcycle.mp h)]
        simp
    _ = -∑ x, if sigma.SameCycle d x then weight x else 0 := by
      rw [Finset.sum_neg_distrib]



theorem fkMedialBoundaryOrbitVisitCount_localMate
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d : FKMedialDart T) :
    permOrbitVisitCount (fkMedialBoundaryStep pairing)
        (fkMedialLocalMate pairing d)
        (fkMedialLocalMate pairing d) =
      permOrbitVisitCount (fkMedialBoundaryStep pairing) d d := by
  let sigma := fkMedialBoundaryStep pairing
  let tau := fkMedialLocalMateEquiv pairing
  let cycleSize (x : FKMedialDart T) : Nat :=
    permCycleClassWeightSum sigma x (fun _ => 1)
  have hsize : cycleSize (tau d) = cycleSize d := by
    unfold cycleSize permCycleClassWeightSum
    calc
      (∑ x, if sigma.SameCycle (tau d) x then 1 else 0) =
          ∑ x, if sigma.SameCycle (tau d) (tau x) then 1 else 0 := by
        exact (tau.sum_comp
          (fun x => if sigma.SameCycle (tau d) x then 1 else 0)).symm
      _ = ∑ x, if sigma.SameCycle d x then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hcycle := fkMedialBoundaryStep_sameCycle_localMate_iff
          pairing d x
        change sigma.SameCycle (tau d) (tau x) ↔
          sigma.SameCycle d x at hcycle
        by_cases h : sigma.SameCycle d x
        · rw [if_pos h, if_pos (hcycle.mpr h)]
        · rw [if_neg h, if_neg (mt hcycle.mp h)]
  have hsizePos : 0 < cycleSize d := by
    unfold cycleSize permCycleClassWeightSum
    rw [Finset.sum_pos_iff]
    exact ⟨d, Finset.mem_univ d,
      by rw [if_pos (Equiv.Perm.SameCycle.refl sigma d)]; exact Nat.zero_lt_one⟩
  have horbit (x : FKMedialDart T) :
      permOrbitWeightSum sigma x (fun _ => (1 : Nat)) = orderOf sigma := by
    unfold permOrbitWeightSum
    simp
  have hleft := permOrbitWeightSum_eq_visitCount_nsmul_cycleSum
    sigma (tau d) (fun _ => (1 : Nat))
  have hright := permOrbitWeightSum_eq_visitCount_nsmul_cycleSum
    sigma d (fun _ => (1 : Nat))
  rw [horbit (tau d)] at hleft
  rw [horbit d] at hright
  change orderOf sigma =
      permOrbitVisitCount sigma (tau d) (tau d) * cycleSize (tau d)
    at hleft
  change orderOf sigma =
      permOrbitVisitCount sigma d d * cycleSize d at hright
  rw [hsize] at hleft
  apply Nat.mul_right_cancel hsizePos
  exact hleft.symm.trans hright

private theorem fkRectMedialBoundaryPrimalSeamTrace_eq_sum_range
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (n : Nat) :
    fkRectMedialBoundaryPrimalSeamTrace R pairing d n =
      ∑ i ∈ Finset.range n,
        fkRectMedialBoundaryPrimalSeamIncrement R pairing
          ((fkMedialBoundaryStep pairing)^[i] d) := by
  induction n generalizing d with
  | zero => simp [fkRectMedialBoundaryPrimalSeamTrace]
  | succ n ih =>
      rw [fkRectMedialBoundaryPrimalSeamTrace, ih,
        Finset.sum_range_succ']
      have htail :
          (∑ i ∈ Finset.range n,
            fkRectMedialBoundaryPrimalSeamIncrement R pairing
              ((fkMedialBoundaryStep pairing)^[i]
                (fkMedialBoundaryStep pairing d))) =
          ∑ i ∈ Finset.range n,
            fkRectMedialBoundaryPrimalSeamIncrement R pairing
              ((fkMedialBoundaryStep pairing)^[i + 1] d) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Function.iterate_succ_apply]
      rw [htail]
      simp only [Function.iterate_zero_apply]
      exact add_comm _ _



theorem fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_visitCount_nsmul
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d) =
      permOrbitVisitCount
          (fkMedialBoundaryStep
            (fkRectConfigurationToMedialPairing R omega)) d d •
        fkRectBoundaryCycleClassWinding R
          (fkRectConfigurationToMedialPairing R omega) d := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  rw [fkRectMedialBoundaryPrimalOrbitWalk_winding]
  change fkRectMedialBoundaryPrimalSeamTrace R pairing d
      (orderOf (fkMedialBoundaryStep pairing)) = _
  rw [fkRectMedialBoundaryPrimalSeamTrace_eq_sum_range]
  rw [← Fin.sum_univ_eq_sum_range]
  change permOrbitWeightSum (fkMedialBoundaryStep pairing) d
      (fkRectMedialBoundaryPrimalSeamIncrement R pairing) = _
  exact permOrbitWeightSum_eq_visitCount_nsmul_cycleSum
    (fkMedialBoundaryStep pairing) d
      (fkRectMedialBoundaryPrimalSeamIncrement R pairing)



theorem fkRectMedialBoundaryPrimalOrbitWalk_winding_localMate
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega
          (fkMedialLocalMate
            (fkRectConfigurationToMedialPairing R omega) d)) =
      -fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  rw [fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_visitCount_nsmul,
    fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_visitCount_nsmul,
    fkMedialBoundaryOrbitVisitCount_localMate,
    fkRectBoundaryCycleClassWinding_localMate]
  exact neg_nsmul _ _

end

end StatMech.FrontierD

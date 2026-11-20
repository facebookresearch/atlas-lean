/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.PermSameCycleWeightSplit
import Code.FrontierD.FKRectBoundaryCycleWeight
import Code.FrontierD.FKRectMedialToggle
import Code.FrontierD.FKMedialBoundaryToggleParity
import Code.FrontierD.FKRectMedialClosedCycles
import Code.FrontierD.FKMedialToggleExact
import Code.FrontierD.FKRectRefinedOpenBoundaryDependence
import Code.FrontierD.FKRectTorusWindingInsertion



open Equiv Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section

private theorem not_windingIndependent_of_pos_nsmul_left
    (n : Nat) (hn : 0 < n) (u v : Int × Int)
    (h : ¬ FKRectWindingIndependent (n • u) v) :
    ¬ FKRectWindingIndependent u v := by
  unfold FKRectWindingIndependent at h ⊢
  push_neg at h ⊢
  rw [Prod.smul_fst, Prod.smul_snd] at h
  simp only [nsmul_eq_mul] at h
  have hnint : (0 : Int) < n := by exact_mod_cast hn
  nlinarith

private theorem not_windingIndependent_nsmul_left
    (n : Nat) (u v : Int × Int)
    (h : ¬ FKRectWindingIndependent u v) :
    ¬ FKRectWindingIndependent (n • u) v := by
  unfold FKRectWindingIndependent at h ⊢
  push_neg at h ⊢
  rw [Prod.smul_fst, Prod.smul_snd]
  simp only [nsmul_eq_mul]
  calc
    (n : Int) * u.1 * v.2 - (n : Int) * u.2 * v.1 =
        (n : Int) * (u.1 * v.2 - u.2 * v.1) := by ring
    _ = 0 := by rw [h]; ring

private theorem not_windingIndependent_add_left
    (u w v : Int × Int)
    (hu : ¬ FKRectWindingIndependent u v)
    (hw : ¬ FKRectWindingIndependent w v) :
    ¬ FKRectWindingIndependent (u + w) v := by
  unfold FKRectWindingIndependent at hu hw ⊢
  push_neg at hu hw ⊢
  simp only [Prod.fst_add, Prod.snd_add]
  linear_combination hu + hw

def fkRectBlackBoundaryWeight (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus) : Int × Int :=
  fkRectMedialBoundaryPrimalSeamIncrement R pairing d.1

def fkRectBlackBoundaryCycleClassWinding
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus) : Int × Int :=
  permCycleClassWeightSum (fkMedialBlackBoundaryPerm pairing) d
    (fkRectBlackBoundaryWeight R pairing)

private theorem fkMedialCheckerColor_eq_of_boundaryStep_sameCycle
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    {d e : FKMedialDart T}
    (hde : (fkMedialBoundaryStep pairing).SameCycle d e) :
    fkMedialCheckerColor d = fkMedialCheckerColor e := by
  obtain ⟨n, hn⟩ := hde.exists_nat_pow_eq
  have hcolor : ∀ n : Nat,
      fkMedialCheckerColor ((fkMedialBoundaryStep pairing)^[n] d) =
        fkMedialCheckerColor d := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        rw [fkMedialCheckerColor_boundaryStep, ih]
  rw [← hn]
  exact (hcolor n).symm

theorem fkRectBoundaryCycleClassWinding_eq_black
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus) :
    fkRectBoundaryCycleClassWinding R pairing d.1 =
      fkRectBlackBoundaryCycleClassWinding R pairing d := by
  classical
  unfold fkRectBoundaryCycleClassWinding
    fkRectBlackBoundaryCycleClassWinding
    permCycleClassWeightSum fkRectBlackBoundaryWeight
  rw [show (∑ x : FKMedialBlackDart R.medialTorus,
        if (fkMedialBlackBoundaryPerm pairing).SameCycle d x then
          fkRectMedialBoundaryPrimalSeamIncrement R pairing x.1 else 0) =
      ∑ x : FKMedialBlackDart R.medialTorus,
        if (fkMedialBoundaryStep pairing).SameCycle d.1 x.1 then
          fkRectMedialBoundaryPrimalSeamIncrement R pairing x.1 else 0 by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [fkMedialBlackBoundaryPerm,
        Equiv.Perm.sameCycle_subtypePerm]]
  let f : FKMedialDart R.medialTorus → Int × Int := fun x =>
    if (fkMedialBoundaryStep pairing).SameCycle d.1 x then
      fkRectMedialBoundaryPrimalSeamIncrement R pairing x else 0
  change (∑ x : FKMedialDart R.medialTorus, f x) =
    ∑ x : FKMedialBlackDart R.medialTorus, f x.1
  calc
    (∑ x : FKMedialDart R.medialTorus, f x) =
        ∑ x ∈ (Finset.univ.filter fun x : FKMedialDart R.medialTorus =>
          fkMedialCheckerColor x = false), f x := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hblack : fkMedialCheckerColor x = false
      · rw [if_pos hblack]
      · rw [if_neg hblack]
        unfold f
        have hnotcycle :
            ¬ (fkMedialBoundaryStep pairing).SameCycle d.1 x := by
          intro hcycle
          apply hblack
          rw [← d.2]
          exact fkMedialCheckerColor_eq_of_boundaryStep_sameCycle
            pairing hcycle.symm
        rw [if_neg hnotcycle]
    _ = ∑ x : FKMedialBlackDart R.medialTorus, f x.1 :=
      Finset.sum_subtype _ (by simp) f

private theorem fkRectHorizontalSeamIncrement_self
    (R : FKRectTorus) (x : R.Vertex) :
    fkRectHorizontalSeamIncrement R x x = 0 := by
  unfold fkRectHorizontalSeamIncrement
  split_ifs with h h
  · rcases h with ⟨h1, h2⟩
    have hw := R.width_gt_two
    omega
  · rcases h with ⟨h1, h2⟩
    omega
  · rfl

private theorem fkRectVerticalSeamIncrement_self
    (R : FKRectTorus) (x : R.Vertex) :
    fkRectVerticalSeamIncrement R x x = 0 := by
  unfold fkRectVerticalSeamIncrement
  split_ifs with h h
  · rcases h with ⟨h1, h2⟩
    have hh := R.height_gt_two
    omega
  · rcases h with ⟨h1, h2⟩
    omega
  · rfl

theorem fkRectBlackBoundaryWeight_toggle_of_ne
    (R : FKRectTorus) (pairing : FKMedialLoopPairing R.medialTorus)
    (v : R.medialTorus.Vertex) (d : FKMedialBlackDart R.medialTorus)
    (hd0 : d ≠ fkMedialBlackDart0 v)
    (hd1 : d ≠ fkMedialBlackDart1 v) :
    fkRectBlackBoundaryWeight R pairing d =
      fkRectBlackBoundaryWeight R (fkMedialTogglePairingAt pairing v) d := by
  rcases d with ⟨⟨w, side⟩, hd⟩
  have hw : w ≠ v := by
    intro hwv
    subst w
    cases side <;> by_cases hp : fkMedialVertexParity v <;>
      simp [fkMedialBlackDart0, fkMedialBlackDart1,
        fkMedialCheckerColor, fkMedialSideVertical, hp] at hd hd0 hd1
  unfold fkRectBlackBoundaryWeight fkRectMedialBoundaryPrimalSeamIncrement
  simp only [fkMedialBoundaryStep_apply]
  simp [fkMedialLocalMate, fkMedialTogglePairingAt, hw]

theorem fkRectBlackBoundaryWeight_closed_dart0_eq_zero
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) :
    fkRectBlackBoundaryWeight R
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F))
        (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)) = 0 := by
  unfold fkRectBlackBoundaryWeight fkRectMedialBoundaryPrimalSeamIncrement
  simp only [fkMedialBoundaryStep_apply,
    fkRectMedialDartPrimalLabel_bondMate]
  have hlocal :
      fkMedialLocalMate
          (fkRectConfigurationToMedialPairing R
            (fkRectConfigurationOfEdges R F))
          (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)).1 =
        fkMedialLocalMate (fkRectClosedMedialPairing R)
          (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)).1 := by
    rcases e with ⟨b, x, y⟩
    cases b <;>
      simp [fkMedialBlackDart0, fkMedialLocalMate,
        fkRectConfigurationToMedialPairing_apply,
        fkRectConfigurationOfEdges, heF,
        fkRectClosedMedialPairing]
  rw [hlocal, fkRectMedialDartPrimalLabel_localMate_closed]
  simp [fkRectHorizontalSeamIncrement_self, fkRectVerticalSeamIncrement_self]

theorem fkRectBlackBoundaryWeight_closed_dart1_eq_zero
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) :
    fkRectBlackBoundaryWeight R
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F))
        (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e)) = 0 := by
  unfold fkRectBlackBoundaryWeight fkRectMedialBoundaryPrimalSeamIncrement
  simp only [fkMedialBoundaryStep_apply,
    fkRectMedialDartPrimalLabel_bondMate]
  have hlocal :
      fkMedialLocalMate
          (fkRectConfigurationToMedialPairing R
            (fkRectConfigurationOfEdges R F))
          (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e)).1 =
        fkMedialLocalMate (fkRectClosedMedialPairing R)
          (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e)).1 := by
    rcases e with ⟨b, x, y⟩
    cases b <;>
      simp [fkMedialBlackDart1, fkMedialLocalMate,
        fkRectConfigurationToMedialPairing_apply,
        fkRectConfigurationOfEdges, heF,
        fkRectClosedMedialPairing]
  rw [hlocal, fkRectMedialDartPrimalLabel_localMate_closed]
  simp [fkRectHorizontalSeamIncrement_self, fkRectVerticalSeamIncrement_self]

theorem fkRectBlackBoundaryWeight_toggle_pair_eq_zero
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) :
    fkRectBlackBoundaryWeight R
          (fkMedialTogglePairingAt
            (fkRectConfigurationToMedialPairing R
              (fkRectConfigurationOfEdges R F))
            (fkRectMedialVertexOfEdge R e))
          (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)) +
        fkRectBlackBoundaryWeight R
          (fkMedialTogglePairingAt
            (fkRectConfigurationToMedialPairing R
              (fkRectConfigurationOfEdges R F))
            (fkRectMedialVertexOfEdge R e))
          (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e)) = 0 := by
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let v := fkRectMedialVertexOfEdge R e
  let a := fkMedialBlackDart0 v
  let b := fkMedialBlackDart1 v
  have hnewv : fkMedialTogglePairingAt pairing v v =
      fkMedialVertexParity v := by
    rw [fkMedialTogglePairingAt_self]
    rw [show pairing v = fkRectClosedMedialPairing R v by
      simp [pairing, fkRectConfigurationToMedialPairing_apply,
        fkRectConfigurationOfEdges, v, heF,
        fkRectClosedMedialPairing]]
    rw [fkRectClosedMedialPairing_eq_not_vertexParity]
    cases fkMedialVertexParity v <;> rfl
  have hnotpair : (! pairing v) = fkMedialVertexParity v := by
    simpa only [fkMedialTogglePairingAt_self] using hnewv
  have hlabel0 :
      fkRectMedialDartPrimalLabel R
          (fkMedialBoundaryStep (fkMedialTogglePairingAt pairing v) a.1) =
        fkRectMedialDartPrimalLabel R b.1 := by
    rw [fkMedialBoundaryStep_apply,
      fkRectMedialDartPrimalLabel_bondMate]
    by_cases hp : fkMedialVertexParity v <;>
      simp [a, b, fkMedialBlackDart0, fkMedialBlackDart1,
        fkMedialLocalMate, hnotpair, fkRectMedialDartPrimalLabel,
        show fkRectClosedPairingAtEdge
            (fkRectTorusMedialEdgeEquiv R v) = !fkMedialVertexParity v by
          exact fkRectClosedMedialPairing_eq_not_vertexParity R v,
        hp]
  have hlabel1 :
      fkRectMedialDartPrimalLabel R
          (fkMedialBoundaryStep (fkMedialTogglePairingAt pairing v) b.1) =
        fkRectMedialDartPrimalLabel R a.1 := by
    rw [fkMedialBoundaryStep_apply,
      fkRectMedialDartPrimalLabel_bondMate]
    by_cases hp : fkMedialVertexParity v <;>
      simp [a, b, fkMedialBlackDart0, fkMedialBlackDart1,
        fkMedialLocalMate, hnotpair, fkRectMedialDartPrimalLabel,
        show fkRectClosedPairingAtEdge
            (fkRectTorusMedialEdgeEquiv R v) = !fkMedialVertexParity v by
          exact fkRectClosedMedialPairing_eq_not_vertexParity R v,
        hp]
  change fkRectMedialBoundaryPrimalSeamIncrement R
      (fkMedialTogglePairingAt pairing v) a.1 +
    fkRectMedialBoundaryPrimalSeamIncrement R
      (fkMedialTogglePairingAt pairing v) b.1 = 0
  unfold fkRectMedialBoundaryPrimalSeamIncrement
  rw [hlabel0, hlabel1]
  apply Prod.ext <;> simp only [Prod.fst_add, Prod.fst_zero,
    Prod.snd_add, Prod.snd_zero]
  · rw [fkRectHorizontalSeamIncrement_swap]
    ring
  · rw [fkRectVerticalSeamIncrement_swap]
    ring

theorem fkRectBlackBoundaryCycleClassWinding_split_of_reachable
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hreach : (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
    fkRectBlackBoundaryCycleClassWinding R
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F))
        (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)) =
      fkRectBlackBoundaryCycleClassWinding R
          (fkRectConfigurationToMedialPairing R
            (fkRectConfigurationOfEdges R (insert e F)))
          (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)) +
        fkRectBlackBoundaryCycleClassWinding R
          (fkRectConfigurationToMedialPairing R
            (fkRectConfigurationOfEdges R (insert e F)))
          (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e)) := by
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let v := fkRectMedialVertexOfEdge R e
  let a := fkMedialBlackDart0 v
  let b := fkMedialBlackDart1 v
  let σ := fkMedialBlackBoundaryPerm pairing
  have habne : a ≠ b := fkMedialBlackDart0_ne_dart1 v
  have hab : σ.SameCycle a b := by
    apply (fkMedial_blackBoundary_sameCycle_iff_reachable pairing a b).2
    exact (fkMedialBlackDarts_reachable_iff_west_east pairing v).2 hreach
  have hcount : StatMech.FrontierA.permCycleCount (σ * Equiv.swap a b) =
      StatMech.FrontierA.permCycleCount σ + 1 := by
    change StatMech.FrontierA.permCycleCount
        (fkMedialBlackBoundaryPerm pairing * fkMedialBlackDartSwap v) =
      StatMech.FrontierA.permCycleCount
        (fkMedialBlackBoundaryPerm pairing) + 1
    rw [← fkMedialBlackBoundaryPerm_toggle pairing v]
    rw [permCycleCount_fkMedialBlackBoundaryPerm,
      permCycleCount_fkMedialBlackBoundaryPerm]
    exact (fkMedialLoopCount_toggle_of_reachable
      R.medialTorus pairing v hreach).symm
  have hweights := permCycleClassWeightSum_split σ a b habne hab hcount
    (fkRectBlackBoundaryWeight R pairing)
    (fkRectBlackBoundaryWeight R (fkMedialTogglePairingAt pairing v))
    (fun d hd0 hd1 => fkRectBlackBoundaryWeight_toggle_of_ne
      R pairing v d hd0 hd1)
    (by
      rw [fkRectBlackBoundaryWeight_closed_dart0_eq_zero R F e heF,
        fkRectBlackBoundaryWeight_closed_dart1_eq_zero R F e heF,
        zero_add,
        fkRectBlackBoundaryWeight_toggle_pair_eq_zero R F e heF])
  unfold fkRectBlackBoundaryCycleClassWinding
  change permCycleClassWeightSum σ a
      (fkRectBlackBoundaryWeight R pairing) = _
  rw [fkRectConfigurationToMedialPairing_insert R F e heF]
  rw [fkMedialBlackBoundaryPerm_toggle]
  exact hweights

theorem fkRectBlackBoundaryCycleClassWinding_eq_insert_of_not_sameCycle
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hreach : (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (d : FKMedialBlackDart R.medialTorus)
    (hd : ¬ (fkMedialBlackBoundaryPerm
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).SameCycle
          (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)) d) :
    fkRectBlackBoundaryCycleClassWinding R
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F)) d =
      fkRectBlackBoundaryCycleClassWinding R
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R (insert e F))) d := by
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let v := fkRectMedialVertexOfEdge R e
  let a := fkMedialBlackDart0 v
  let b := fkMedialBlackDart1 v
  let σ := fkMedialBlackBoundaryPerm pairing
  have habne : a ≠ b := fkMedialBlackDart0_ne_dart1 v
  have hab : σ.SameCycle a b := by
    apply (fkMedial_blackBoundary_sameCycle_iff_reachable pairing a b).2
    exact (fkMedialBlackDarts_reachable_iff_west_east pairing v).2 hreach
  have hcount : StatMech.FrontierA.permCycleCount (σ * Equiv.swap a b) =
      StatMech.FrontierA.permCycleCount σ + 1 := by
    change StatMech.FrontierA.permCycleCount
        (fkMedialBlackBoundaryPerm pairing * fkMedialBlackDartSwap v) =
      StatMech.FrontierA.permCycleCount
        (fkMedialBlackBoundaryPerm pairing) + 1
    rw [← fkMedialBlackBoundaryPerm_toggle pairing v]
    rw [permCycleCount_fkMedialBlackBoundaryPerm,
      permCycleCount_fkMedialBlackBoundaryPerm]
    exact (fkMedialLoopCount_toggle_of_reachable
      R.medialTorus pairing v hreach).symm
  have hweights := permCycleClassWeightSum_eq_of_not_sameCycle
    σ a b d habne hab hcount hd
    (fkRectBlackBoundaryWeight R pairing)
    (fkRectBlackBoundaryWeight R (fkMedialTogglePairingAt pairing v))
    (fun x hx0 hx1 => fkRectBlackBoundaryWeight_toggle_of_ne
      R pairing v x hx0 hx1)
  unfold fkRectBlackBoundaryCycleClassWinding
  change permCycleClassWeightSum σ d
      (fkRectBlackBoundaryWeight R pairing) = _
  rw [fkRectConfigurationToMedialPairing_insert R F e heF]
  rw [fkMedialBlackBoundaryPerm_toggle]
  exact hweights

private theorem fkRectBlackBoundaryCycleClassWinding_eq_of_sameCycle
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d e : FKMedialBlackDart R.medialTorus)
    (hde : (fkMedialBlackBoundaryPerm pairing).SameCycle d e) :
    fkRectBlackBoundaryCycleClassWinding R pairing d =
      fkRectBlackBoundaryCycleClassWinding R pairing e := by
  classical
  unfold fkRectBlackBoundaryCycleClassWinding
    permCycleClassWeightSum
  apply Finset.sum_congr rfl
  intro x hx
  have hiff :
      (fkMedialBlackBoundaryPerm pairing).SameCycle d x ↔
        (fkMedialBlackBoundaryPerm pairing).SameCycle e x := by
    constructor
    · exact fun h => hde.symm.trans h
    · exact fun h => hde.trans h
  by_cases hdx : (fkMedialBlackBoundaryPerm pairing).SameCycle d x
  · simp [hdx, hiff.mp hdx]
  · have hex : ¬ (fkMedialBlackBoundaryPerm pairing).SameCycle e x :=
      fun h => hdx (hiff.mpr h)
    rw [if_neg hdx, if_neg hex]

private theorem fkRectInsertedWalk_newBlackCycle_dependent
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (heF : e ∉ F) (d : FKMedialBlackDart R.medialTorus) :
    ¬ FKRectWindingIndependent
      (fkRectBlackBoundaryCycleClassWinding R
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R (insert e F))) d)
      (fkRectWalkWinding R
        (fkRectInsertedFundamentalWalk R F e r)) := by
  have horbit := fkRect_boundaryOrbit_winding_dependent_of_openWalk
    R (insert e F) (fkRectInsertedFundamentalWalk R F e r) d.1
  rw [fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_visitCount_nsmul,
    fkRectBoundaryCycleClassWinding_eq_black] at horbit
  exact not_windingIndependent_of_pos_nsmul_left
    (permOrbitVisitCount
      (fkMedialBoundaryStep
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R (insert e F)))) d.1 d.1)
    (permOrbitVisitCount_self_pos
      (fkMedialBoundaryStep
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R (insert e F)))) d.1)
    _ _ horbit

theorem fkRectInsertedWalk_oldBlackCycle_dependent_of_reachable
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (heF : e ∉ F)
    (hreach : (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (d : FKMedialBlackDart R.medialTorus) :
    ¬ FKRectWindingIndependent
      (fkRectBlackBoundaryCycleClassWinding R
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F)) d)
      (fkRectWalkWinding R
        (fkRectInsertedFundamentalWalk R F e r)) := by
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let v := fkRectMedialVertexOfEdge R e
  let a := fkMedialBlackDart0 v
  let b := fkMedialBlackDart1 v
  by_cases had : (fkMedialBlackBoundaryPerm pairing).SameCycle a d
  · have hdepa := fkRectInsertedWalk_newBlackCycle_dependent
      R F e r heF a
    have hdepb := fkRectInsertedWalk_newBlackCycle_dependent
      R F e r heF b
    have hsum := not_windingIndependent_add_left _ _ _ hdepa hdepb
    have hsplit := fkRectBlackBoundaryCycleClassWinding_split_of_reachable
      R F e heF hreach
    have hda := fkRectBlackBoundaryCycleClassWinding_eq_of_sameCycle
      R pairing d a had.symm
    rw [hda, hsplit]
    exact hsum
  · have hnew := fkRectInsertedWalk_newBlackCycle_dependent
      R F e r heF d
    rw [fkRectBlackBoundaryCycleClassWinding_eq_insert_of_not_sameCycle
      R F e heF hreach d had]
    exact hnew

theorem fkRectInsertedWalk_oldBlackBoundaryOrbit_dependent_of_reachable
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (heF : e ∉ F)
    (hreach : (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (d : FKMedialBlackDart R.medialTorus) :
    ¬ FKRectWindingIndependent
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R
          (fkRectConfigurationOfEdges R F) d.1))
      (fkRectWalkWinding R
        (fkRectInsertedFundamentalWalk R F e r)) := by
  rw [fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_visitCount_nsmul,
    fkRectBoundaryCycleClassWinding_eq_black]
  exact not_windingIndependent_nsmul_left _ _ _
    (fkRectInsertedWalk_oldBlackCycle_dependent_of_reachable
      R F e r heF hreach d)

end

end StatMech.FrontierD

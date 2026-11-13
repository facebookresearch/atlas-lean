/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectMedialReachability
import Code.FrontierD.FKMedialBoundaryPermutation
import Code.FrontierD.FKRectTorusSquareCoverIntersection











open SimpleGraph

namespace StatMech.FrontierD

noncomputable section



theorem fkRectMedialDartPrimalLabel_localMate_eq_or_adj
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    fkRectMedialDartPrimalLabel R d =
        fkRectMedialDartPrimalLabel R
          (fkMedialLocalMate
            (fkRectConfigurationToMedialPairing R omega) d) ∨
      (fkRectOpenGraph R omega).Adj
        (fkRectMedialDartPrimalLabel R d)
        (fkRectMedialDartPrimalLabel R
          (fkMedialLocalMate
            (fkRectConfigurationToMedialPairing R omega) d)) := by
  rcases d with ⟨v, side⟩
  let e := fkRectTorusMedialEdgeEquiv R v
  have hedge : fkRectTorusIndexedEdge R e =
      s(fkRectMedialWestPrimal R e, fkRectMedialEastPrimal R e) :=
    fkRectTorusIndexedEdge_eq_medialPrimals R e
  have hcross (ho : omega e = true) :
      (fkRectOpenGraph R omega).Adj
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e) :=
    ⟨e, ho, hedge⟩
  cases hopen : omega e <;>
    cases hp : fkRectClosedPairingAtEdge e <;> cases side
  all_goals
    simp only [fkRectConfigurationToMedialPairing_apply, e] at *
  all_goals
    simp [fkRectMedialDartPrimalLabel, fkMedialLocalMate, hopen, hp]
  all_goals
    first
    | exact Or.inl rfl
    | exact Or.inr (hcross hopen)
    | exact Or.inr (hcross hopen).symm



theorem fkRectMedialDartPrimalLabel_boundaryStep_eq_or_adj
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    fkRectMedialDartPrimalLabel R d =
        fkRectMedialDartPrimalLabel R
          (fkMedialBoundaryStep
            (fkRectConfigurationToMedialPairing R omega) d) ∨
      (fkRectOpenGraph R omega).Adj
        (fkRectMedialDartPrimalLabel R d)
        (fkRectMedialDartPrimalLabel R
          (fkMedialBoundaryStep
            (fkRectConfigurationToMedialPairing R omega) d)) := by
  have h := fkRectMedialDartPrimalLabel_localMate_eq_or_adj R omega d
  rw [fkMedialBoundaryStep_apply,
    fkRectMedialDartPrimalLabel_bondMate] at ⊢
  exact h


noncomputable def fkRectMedialBoundaryPrimalStepWalk
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    (fkRectOpenGraph R omega).Walk
      (fkRectMedialDartPrimalLabel R d)
      (fkRectMedialDartPrimalLabel R
        (fkMedialBoundaryStep
          (fkRectConfigurationToMedialPairing R omega) d)) := by
  classical
  by_cases heq : fkRectMedialDartPrimalLabel R d =
      fkRectMedialDartPrimalLabel R
        (fkMedialBoundaryStep
          (fkRectConfigurationToMedialPairing R omega) d)
  · exact (.nil : (fkRectOpenGraph R omega).Walk
      (fkRectMedialDartPrimalLabel R d)
      (fkRectMedialDartPrimalLabel R d)).copy rfl heq
  · exact .cons
      ((fkRectMedialDartPrimalLabel_boundaryStep_eq_or_adj R omega d).resolve_left heq)
      .nil

theorem fkRectMedialBoundaryPrimalStepWalk_length_le_one
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    (fkRectMedialBoundaryPrimalStepWalk R omega d).length ≤ 1 := by
  unfold fkRectMedialBoundaryPrimalStepWalk
  split <;> simp


noncomputable def fkRectMedialBoundaryPrimalTrace
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    (n : Nat) → (fkRectOpenGraph R omega).Walk
      (fkRectMedialDartPrimalLabel R d)
      (fkRectMedialDartPrimalLabel R
        ((fkMedialBoundaryStep
          (fkRectConfigurationToMedialPairing R omega))^[n] d))
  | 0 => .nil
  | n + 1 => by
      let step := fkRectMedialBoundaryPrimalStepWalk R omega d
      let tail := fkRectMedialBoundaryPrimalTrace R omega
        (fkMedialBoundaryStep
          (fkRectConfigurationToMedialPairing R omega) d) n
      have joined := step.append tail
      simpa only [Function.iterate_succ_apply] using joined


noncomputable def fkRectMedialBoundaryPrimalOrbitWalk
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    (fkRectOpenGraph R omega).Walk
      (fkRectMedialDartPrimalLabel R d)
      (fkRectMedialDartPrimalLabel R d) := by
  let sigma := fkMedialBoundaryStep
    (fkRectConfigurationToMedialPairing R omega)
  let p := fkRectMedialBoundaryPrimalTrace R omega d (orderOf sigma)
  have hsigma : sigma ^ orderOf sigma = 1 := pow_orderOf_eq_one sigma
  have hreturn : sigma^[orderOf sigma] d = d := by
    rw [← Equiv.Perm.coe_pow]
    simpa only [hsigma, Equiv.Perm.one_apply]
  exact p.copy rfl (congrArg (fkRectMedialDartPrimalLabel R) hreturn)

end

end StatMech.FrontierD

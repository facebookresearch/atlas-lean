/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectCutPushforward










namespace StatMech.FrontierD

noncomputable section


def fkRectEdgeToDualEdge (R : FKRectTorus) (e : R.EdgeIndex) : R.EdgeIndex :=
  if e.1 then
    (false, e.2)
  else
    (true, (SixVertexArrows.cyclicPred R.width_pos e.2.1, e.2.2))


def fkRectDualEdgeToEdge (R : FKRectTorus) (e : R.EdgeIndex) : R.EdgeIndex :=
  if e.1 then
    (false, (finitePeriodicSucc R.width_pos e.2.1, e.2.2))
  else
    (true, e.2)

@[simp] theorem fkRectDualEdgeToEdge_edgeToDualEdge
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectDualEdgeToEdge R (fkRectEdgeToDualEdge R e) = e := by
  rcases e with ⟨b, x, y⟩
  cases b
  · simp [fkRectEdgeToDualEdge, fkRectDualEdgeToEdge,
      finitePeriodicSucc_cyclicPred]
  · rfl

@[simp] theorem fkRectEdgeToDualEdge_dualEdgeToEdge
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectEdgeToDualEdge R (fkRectDualEdgeToEdge R e) = e := by
  rcases e with ⟨b, x, y⟩
  cases b
  · rfl
  · simp [fkRectEdgeToDualEdge, fkRectDualEdgeToEdge,
      svCyclicPred_finitePeriodicSucc]


def fkRectEdgeDualEquiv (R : FKRectTorus) : R.EdgeIndex ≃ R.EdgeIndex where
  toFun := fkRectEdgeToDualEdge R
  invFun := fkRectDualEdgeToEdge R
  left_inv := fkRectDualEdgeToEdge_edgeToDualEdge R
  right_inv := fkRectEdgeToDualEdge_dualEdgeToEdge R

@[simp] theorem fkRectEdgeDualEquiv_apply
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectEdgeDualEquiv R e = fkRectEdgeToDualEdge R e := rfl

@[simp] theorem fkRectEdgeDualEquiv_symm_apply
    (R : FKRectTorus) (e : R.EdgeIndex) :
    (fkRectEdgeDualEquiv R).symm e = fkRectDualEdgeToEdge R e := rfl



def fkRectDualConfigurationEquiv (R : FKRectTorus) :
    R.Configuration ≃ R.Configuration :=
  Equiv.arrowCongr (fkRectEdgeDualEquiv R) Equiv.boolNot

@[simp] theorem fkRectDualConfigurationEquiv_apply
    (R : FKRectTorus) (omega : R.Configuration) (e : R.EdgeIndex) :
    fkRectDualConfigurationEquiv R omega e =
      !(omega (fkRectDualEdgeToEdge R e)) := rfl

theorem fkRectDualConfigurationEquiv_apply_edgeToDualEdge
    (R : FKRectTorus) (omega : R.Configuration) (e : R.EdgeIndex) :
    fkRectDualConfigurationEquiv R omega (fkRectEdgeToDualEdge R e) =
      !(omega e) := by
  simp

theorem fkRectDualConfiguration_open_iff_primal_closed
    (R : FKRectTorus) (omega : R.Configuration) (e : R.EdgeIndex) :
    fkRectDualConfigurationEquiv R omega (fkRectEdgeToDualEdge R e) = true ↔
      omega e = false := by
  rw [fkRectDualConfigurationEquiv_apply_edgeToDualEdge]
  cases omega e <;> simp


theorem fkRectDualConfigurationEquiv_antitone (R : FKRectTorus) :
    Antitone (fkRectDualConfigurationEquiv R) := by
  intro omega tau hot e
  rw [fkRectDualConfigurationEquiv_apply,
    fkRectDualConfigurationEquiv_apply]
  have h := hot (fkRectDualEdgeToEdge R e)
  cases homega : omega (fkRectDualEdgeToEdge R e) <;>
    cases htau : tau (fkRectDualEdgeToEdge R e) <;>
    simp_all

end

end StatMech.FrontierD

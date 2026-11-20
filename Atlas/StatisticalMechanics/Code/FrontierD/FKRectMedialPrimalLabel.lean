/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKMedialToggleCount

namespace StatMech.FrontierD

@[simp] theorem fkRectMedialVertexOfEdge_fst_val
    (R : FKRectTorus) (e : R.EdgeIndex) :
    (fkRectMedialVertexOfEdge R e).1.val =
      e.1.toNat + 2 * e.2.1.val := by
  rcases e with ⟨b, x, y⟩
  cases b <;> rfl

@[simp] theorem fkRectMedialVertexOfEdge_snd
    (R : FKRectTorus) (e : R.EdgeIndex) :
    (fkRectMedialVertexOfEdge R e).2 = e.2.2 := by
  rcases e with ⟨b, x, y⟩
  cases b <;> rfl

@[simp] theorem fkRectTorusMedialEdgeEquiv_symm_fst_val
    (R : FKRectTorus) (e : R.EdgeIndex) :
    ((fkRectTorusMedialEdgeEquiv R).symm e).1.val =
      e.1.toNat + 2 * e.2.1.val :=
  fkRectMedialVertexOfEdge_fst_val R e

@[simp] theorem fkRectTorusMedialEdgeEquiv_symm_snd
    (R : FKRectTorus) (e : R.EdgeIndex) :
    ((fkRectTorusMedialEdgeEquiv R).symm e).2 = e.2.2 :=
  fkRectMedialVertexOfEdge_snd R e


def fkRectMedialWestPrimal (R : FKRectTorus) (e : R.EdgeIndex) : R.Vertex :=
  if e.1 then
    if Even e.2.2.val then e.2
    else (e.2.1, SixVertexArrows.cyclicPred R.height_pos e.2.2)
  else if Even e.2.2.val then
    (SixVertexArrows.cyclicPred R.width_pos e.2.1,
      SixVertexArrows.cyclicPred R.height_pos e.2.2)
  else
    (SixVertexArrows.cyclicPred R.width_pos e.2.1, e.2.2)


def fkRectMedialEastPrimal (R : FKRectTorus) (e : R.EdgeIndex) : R.Vertex :=
  if e.1 then
    if Even e.2.2.val then
      (e.2.1, SixVertexArrows.cyclicPred R.height_pos e.2.2)
    else e.2
  else if Even e.2.2.val then e.2
  else (e.2.1, SixVertexArrows.cyclicPred R.height_pos e.2.2)



theorem fkRectTorusIndexedEdge_eq_medialPrimals
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectTorusIndexedEdge R e =
      s(fkRectMedialWestPrimal R e, fkRectMedialEastPrimal R e) := by
  rcases e with ⟨b, x, y⟩
  cases b <;> by_cases hy : Even y.val <;>
    simp [fkRectTorusIndexedEdge, fkRectMedialWestPrimal,
      fkRectMedialEastPrimal, hy, Sym2.eq_swap]



def fkRectMedialDartPrimalLabel (R : FKRectTorus)
    (d : FKMedialDart R.medialTorus) : R.Vertex :=
  let e := fkRectTorusMedialEdgeEquiv R d.1
  match d.2 with
  | .west => fkRectMedialWestPrimal R e
  | .east => fkRectMedialEastPrimal R e
  | .south =>
      if fkRectClosedPairingAtEdge e then
        fkRectMedialWestPrimal R e
      else fkRectMedialEastPrimal R e
  | .north =>
      if fkRectClosedPairingAtEdge e then
        fkRectMedialEastPrimal R e
      else fkRectMedialWestPrimal R e



def fkRectClosedMedialPairing (R : FKRectTorus) :
    FKMedialLoopPairing R.medialTorus :=
  fun v => fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R v)


theorem fkRectMedialDartPrimalLabel_localMate_closed
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    fkRectMedialDartPrimalLabel R
        (fkMedialLocalMate (fkRectClosedMedialPairing R) d) =
      fkRectMedialDartPrimalLabel R d := by
  rcases d with ⟨v, side⟩
  cases hp : fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R v) <;>
    cases side <;>
    simp [fkRectMedialDartPrimalLabel, fkRectClosedMedialPairing,
      fkMedialLocalMate, hp]



theorem fkRectMedialDartPrimalLabel_localMate_reachable
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    (fkRectOpenGraph R omega).Reachable
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
      (fkRectOpenGraph R omega).Reachable
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e) :=
    (show (fkRectOpenGraph R omega).Adj
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e) from
      ⟨e, ho, hedge⟩).reachable
  cases hopen : omega e <;>
    cases hp : fkRectClosedPairingAtEdge e <;> cases side
  all_goals
    simp only [fkRectConfigurationToMedialPairing_apply, e] at *
  all_goals
    simp [fkRectMedialDartPrimalLabel, fkMedialLocalMate, hopen, hp]
  all_goals
    first
    | exact SimpleGraph.Reachable.refl _
    | exact hcross hopen
    | exact (hcross hopen).symm

end StatMech.FrontierD

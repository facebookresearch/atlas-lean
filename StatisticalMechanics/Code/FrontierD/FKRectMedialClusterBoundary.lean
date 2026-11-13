/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectMedialReachability
import Code.FrontierD.FKRectTorusRibbonReduction
import Code.FrontierD.FKRectEulerDefectClassification

open SimpleGraph

namespace StatMech.FrontierD

noncomputable section


def fkRectMedialDartAtPrimalVertex (R : FKRectTorus) (x : R.Vertex) :
    FKMedialDart R.medialTorus :=
  let e : R.EdgeIndex := (true, x)
  if Even x.2.val then
    fkMedialWestDart (fkRectMedialVertexOfEdge R e)
  else
    fkMedialEastDart (fkRectMedialVertexOfEdge R e)

@[simp] theorem fkRectMedialDartPrimalLabel_dartAtPrimalVertex
    (R : FKRectTorus) (x : R.Vertex) :
    fkRectMedialDartPrimalLabel R
      (fkRectMedialDartAtPrimalVertex R x) = x := by
  by_cases hx : Even x.2.val <;>
    simp [fkRectMedialDartAtPrimalVertex,
      fkRectMedialDartPrimalLabel_west_vertexOfEdge,
      fkRectMedialDartPrimalLabel_east_vertexOfEdge,
      fkRectMedialWestPrimal, fkRectMedialEastPrimal, hx]




def fkRectMedialComponentToPrimalComponent
    (R : FKRectTorus) (omega : R.Configuration) :
    (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).ConnectedComponent ->
      (fkRectOpenGraph R omega).ConnectedComponent :=
  ConnectedComponent.lift
    (fun d => (fkRectOpenGraph R omega).connectedComponentMk
      (fkRectMedialDartPrimalLabel R d))
    (by
      intro d e p hp
      apply ConnectedComponent.sound
      exact fkRectMedial_reachable_primalLabel_reachable R omega ⟨p⟩)

@[simp] theorem fkRectMedialComponentToPrimalComponent_mk
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    fkRectMedialComponentToPrimalComponent R omega
        ((fkMedialLoopGraph R.medialTorus
          (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk d) =
      (fkRectOpenGraph R omega).connectedComponentMk
        (fkRectMedialDartPrimalLabel R d) :=
  rfl


theorem fkRectMedialComponentToPrimalComponent_surjective
    (R : FKRectTorus) (omega : R.Configuration) :
    Function.Surjective (fkRectMedialComponentToPrimalComponent R omega) := by
  intro C
  induction C using ConnectedComponent.ind with
  | _ x =>
      refine ⟨(fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (fkRectMedialDartAtPrimalVertex R x), ?_⟩
      simp



theorem fkRectNumClusters_le_medialLoopCount
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectNumClusters R omega <= fkRectMedialLoopCount R omega := by
  have h := Nat.card_le_card_of_surjective
    (fkRectMedialComponentToPrimalComponent R omega)
    (fkRectMedialComponentToPrimalComponent_surjective R omega)
  simpa [fkRectNumClusters, fkRectMedialLoopCount, fkMedialLoopCount,
    Nat.card_eq_fintype_card] using h




theorem fkRectEulerHomologyDefect_le_cycleRankInt
    (R : FKRectTorus) (F : Finset R.EdgeIndex) :
    fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) <=
      (F.card : Int) + (fkRectFinsetClusterCount R F : Int) -
        (Fintype.card R.Vertex : Int) := by
  have hcount := fkRectNumClusters_le_medialLoopCount R
    (fkRectConfigurationOfEdges R F)
  have hcountInt : (fkRectFinsetClusterCount R F : Int) <=
      (fkRectMedialLoopCount R
        (fkRectConfigurationOfEdges R F) : Int) := by
    exact_mod_cast hcount
  rw [fkRectEulerHomologyDefect_configurationOfEdges]
  omega



theorem fkRectEulerHomologyDefect_eq_zero_of_cycleRankInt_le_one
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    (hrank : (F.card : Int) + (fkRectFinsetClusterCount R F : Int) -
        (Fintype.card R.Vertex : Int) <= 1) :
    fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 0 := by
  rcases fkRectEulerHomologyDefect_classified R F with hzero | htwo
  · exact hzero
  · have hle := fkRectEulerHomologyDefect_le_cycleRankInt R F
    rw [htwo] at hle
    omega



theorem fkRectCycleRankInt_ge_two_of_eulerHomologyDefect_eq_two
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    (hdefect : fkRectEulerHomologyDefect R
      (fkRectConfigurationOfEdges R F) = 2) :
    2 <= (F.card : Int) + (fkRectFinsetClusterCount R F : Int) -
      (Fintype.card R.Vertex : Int) := by
  have hle := fkRectEulerHomologyDefect_le_cycleRankInt R F
  rwa [hdefect] at hle

end

end StatMech.FrontierD

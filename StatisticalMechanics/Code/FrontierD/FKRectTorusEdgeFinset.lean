/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectTorusRibbonCounts
import Code.FrontierD.FKRectTorusRandomCluster
import Code.Lattice.EulerFaces2

open Finset SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section


def fkRectOpenEdges (R : FKRectTorus) (omega : R.Configuration) :
    Finset R.EdgeIndex :=
  Finset.univ.filter fun a => omega a = true


def fkRectConfigurationOfEdges (R : FKRectTorus)
    (F : Finset R.EdgeIndex) : R.Configuration :=
  fun a => decide (a ∈ F)

@[simp] theorem fkRectConfigurationOfEdges_apply
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (a : R.EdgeIndex) :
    fkRectConfigurationOfEdges R F a = true ↔ a ∈ F := by
  simp [fkRectConfigurationOfEdges]

@[simp] theorem fkRectOpenEdges_configurationOfEdges
    (R : FKRectTorus) (F : Finset R.EdgeIndex) :
    fkRectOpenEdges R (fkRectConfigurationOfEdges R F) = F := by
  classical
  ext a
  simp [fkRectOpenEdges]

@[simp] theorem fkRectConfigurationOfEdges_openEdges
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectConfigurationOfEdges R (fkRectOpenEdges R omega) = omega := by
  classical
  funext a
  cases h : omega a <;> simp [fkRectConfigurationOfEdges, fkRectOpenEdges, h]



def fkRectConfigurationEdgeFinsetEquiv (R : FKRectTorus) :
    R.Configuration ≃ Finset R.EdgeIndex where
  toFun := fkRectOpenEdges R
  invFun := fkRectConfigurationOfEdges R
  left_inv := fkRectConfigurationOfEdges_openEdges R
  right_inv := fkRectOpenEdges_configurationOfEdges R

theorem fkRectOpenEdgeCount_configurationOfEdges
    (R : FKRectTorus) (F : Finset R.EdgeIndex) :
    fkRectOpenEdgeCount R (fkRectConfigurationOfEdges R F) = F.card := by
  unfold fkRectOpenEdgeCount
  rw [show (Finset.univ.filter fun a : R.EdgeIndex =>
      fkRectConfigurationOfEdges R F a = true) = F by
    simpa [fkRectOpenEdges] using fkRectOpenEdges_configurationOfEdges R F]

@[simp] theorem fkRectOpenGraph_configurationOfEdges_adj
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (x y : R.Vertex) :
    (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Adj x y ↔
      ∃ a ∈ F, fkRectTorusIndexedEdge R a = s(x, y) := by
  simp [fkRectOpenGraph, fkRectConfigurationOfEdges]

theorem fkRectOpenGraph_configurationOfEdges_empty (R : FKRectTorus) :
    fkRectOpenGraph R (fkRectConfigurationOfEdges R ∅) = ⊥ := by
  ext x y
  simp

theorem fkRectOpenGraph_configurationOfEdges_univ (R : FKRectTorus) :
    fkRectOpenGraph R (fkRectConfigurationOfEdges R Finset.univ) =
      fkRectTorusGraph R := by
  ext x y
  simp [fkRectTorusGraph]



def fkRectFinsetClusterCount (R : FKRectTorus)
    (F : Finset R.EdgeIndex) : Nat :=
  fkRectNumClusters R (fkRectConfigurationOfEdges R F)

theorem fkRectFinsetClusterCount_empty (R : FKRectTorus) :
    fkRectFinsetClusterCount R ∅ = Fintype.card R.Vertex := by
  unfold fkRectFinsetClusterCount fkRectNumClusters
  let G := fkRectOpenGraph R (fkRectConfigurationOfEdges R ∅)
  have hG : G = (⊥ : SimpleGraph R.Vertex) :=
    fkRectOpenGraph_configurationOfEdges_empty R
  calc
    Fintype.card G.ConnectedComponent =
        Fintype.card (⊥ : SimpleGraph R.Vertex).ConnectedComponent := by
      exact Fintype.card_congr
        (Equiv.cast (congrArg
          (fun H : SimpleGraph R.Vertex => H.ConnectedComponent) hG))
    _ = Fintype.card R.Vertex := by
      simpa only [Nat.card_eq_fintype_card] using
        (card_components_bot (V := R.Vertex))

end

end StatMech.FrontierD

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Code.FrontierA.IsoradialCellularRibbonDuality










namespace StatMech.FrontierA

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


abbrev finiteGraphEdge := {edge : Sym2 V // edge ∈ G.edgeFinset}


noncomputable def finiteGraphEdge.dart (edge : finiteGraphEdge G) : G.Dart := by
  have hedgeSet : edge.1 ∈ G.edgeSet :=
    SimpleGraph.mem_edgeFinset.mp edge.2
  have hcard := G.dart_edge_fiber_card edge.1 hedgeSet
  have hnonempty :
      ({dart : G.Dart | dart.edge = edge.1} : Finset G.Dart).Nonempty := by
    apply Finset.card_pos.mp
    omega
  exact hnonempty.choose

@[simp]
theorem finiteGraphEdge.dart_edge (edge : finiteGraphEdge G) :
    (edge.dart G).edge = edge.1 := by
  have hedgeSet : edge.1 ∈ G.edgeSet :=
    SimpleGraph.mem_edgeFinset.mp edge.2
  have hcard := G.dart_edge_fiber_card edge.1 hedgeSet
  have hnonempty :
      ({dart : G.Dart | dart.edge = edge.1} : Finset G.Dart).Nonempty := by
    apply Finset.card_pos.mp
    omega
  exact Finset.mem_filter.mp hnonempty.choose_spec |>.2


noncomputable def finiteGraphEdge.edgeFlip
    (edge : finiteGraphEdge G) : Equiv.Perm G.Dart :=
  Equiv.swap (edge.dart G) (edge.dart G).symm

theorem finiteGraphEdge.edgeFlip_isSwap (edge : finiteGraphEdge G) :
    (edge.edgeFlip G).IsSwap := by
  rw [finiteGraphEdge.edgeFlip, Equiv.Perm.swap_isSwap_iff]
  exact (edge.dart G).symm_ne.symm

theorem finiteGraphEdge.dart_edge_ne {edge edge' : finiteGraphEdge G}
    (hne : edge ≠ edge') : (edge.dart G).edge ≠ (edge'.dart G).edge := by
  rw [finiteGraphEdge.dart_edge, finiteGraphEdge.dart_edge]
  exact fun h => hne (Subtype.ext h)

theorem finiteGraphEdge.edgeFlip_disjoint {edge edge' : finiteGraphEdge G}
    (hne : edge ≠ edge') :
    (edge.edgeFlip G).Disjoint (edge'.edgeFlip G) := by
  let a := edge.dart G
  let b := edge'.dart G
  have habEdge : a.edge ≠ b.edge :=
    finiteGraphEdge.dart_edge_ne G hne
  have hab : a ≠ b := fun h => habEdge (congrArg Dart.edge h)
  have habs : a ≠ b.symm := fun h =>
    habEdge (by rw [h, Dart.edge_symm])
  have hasb : a.symm ≠ b := fun h =>
    habEdge (by rw [← h, Dart.edge_symm])
  have hasbs : a.symm ≠ b.symm := fun h =>
    habEdge (by
      rw [← Dart.edge_symm a, ← Dart.edge_symm b, h])
  have hnodup : [a, a.symm, b, b.symm].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or]
    exact ⟨⟨a.symm_ne.symm, hab, habs⟩,
      ⟨⟨hasb, hasbs⟩,
        ⟨b.symm_ne.symm, ⟨by simp, List.nodup_nil⟩⟩⟩⟩
  exact Equiv.Perm.disjoint_swap_swap hnodup

theorem finiteGraphEdge.edgeFlip_commute {edge edge' : finiteGraphEdge G}
    (hne : edge ≠ edge') :
    Commute (edge.edgeFlip G) (edge'.edgeFlip G) :=
  (finiteGraphEdge.edgeFlip_disjoint G hne).commute




structure FiniteCellularGraphEmbedding where
  rotation : Equiv.Perm G.Dart
  rotation_fst : forall dart, (rotation dart).fst = dart.fst
  rotationCycles_eq_vertices :
    permCycleCount rotation = Fintype.card V
  faceCount : Nat
  genus : Nat
  cellularEuler :
    Fintype.card V + faceCount + 2 * genus = G.edgeFinset.card + 2

namespace FiniteCellularGraphEmbedding



noncomputable def ribbonSystem (embedding : FiniteCellularGraphEmbedding G) :
    RibbonPermutationSystem (finiteGraphEdge G) G.Dart where
  rotation := embedding.rotation
  edgeFlip := finiteGraphEdge.edgeFlip G
  edgeFlip_isSwap := finiteGraphEdge.edgeFlip_isSwap G
  edgeFlip_commute := by
    intro edge edge' hne
    exact finiteGraphEdge.edgeFlip_commute G hne


noncomputable def cellularDualData
    (embedding : FiniteCellularGraphEmbedding G) :
    CellularRibbonDualData embedding.ribbonSystem where
  primalVertexCount := Fintype.card V
  dualVertexCount := embedding.faceCount
  genus := embedding.genus
  rotationCycles_eq_primalVertexCount :=
    embedding.rotationCycles_eq_vertices
  cellularEuler := by
    simpa using embedding.cellularEuler

theorem ribbonSystem_boundaryParity
    (embedding : FiniteCellularGraphEmbedding G) :
    forall edges : Finset (finiteGraphEdge G),
      (edgesᶜ.card + embedding.ribbonSystem.boundaryComponents edges) % 2 =
        embedding.faceCount % 2 :=
  embedding.cellularDualData.boundaryParity



theorem isoradialCritical_subgraphSum_duality
    (embedding : FiniteCellularGraphEmbedding G)
    (character : forall F : Finset (finiteGraphEdge G),
      Fin (embedding.ribbonSystem.boundaryComponents F) -> Complex)
    (hcharacter : forall (F : Finset (finiteGraphEdge G))
      (boundary : Fin (embedding.ribbonSystem.boundaryComponents F)),
        character F boundary ≠ 0)
    (htotal : forall F : Finset (finiteGraphEdge G),
      ∏ boundary, character F boundary = 1)
    (theta : finiteGraphEdge G -> Real)
    (htheta : forall edge, 0 < theta edge)
    (htheta' : forall edge, theta edge < Real.pi / 2) :
    kwDualSubgraphSum
        (dualRibbonBoundaryCharacterCoefficient
          embedding.ribbonSystem character)
        (fun edge => isoradialCriticalMu (Real.pi / 2 - theta edge)) =
      (-1 : Complex) ^ embedding.faceCount *
        ((∏ edge : finiteGraphEdge G,
            isoradialCriticalMu (theta edge))⁻¹ *
          kwDualSubgraphSum
            (ribbonBoundaryCharacterCoefficient
              embedding.ribbonSystem character)
            (fun edge => isoradialCriticalMu (theta edge))) := by
  exact cellularRibbon_isoradialCritical_subgraphSum_duality
    embedding.ribbonSystem embedding.cellularDualData character
      hcharacter htotal theta htheta htheta'

end FiniteCellularGraphEmbedding

end StatMech.FrontierA

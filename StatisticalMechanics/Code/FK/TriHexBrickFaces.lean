/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexBrickPlanar











open SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls



def hexagonalBrickFaceLeft (t : Site 2) : Site 2 :=
  ![2 * t 0 + t 1 - 2, -t 1]


def hexagonalBrickFaceRight (t : Site 2) : Site 2 :=
  ![2 * t 0 + t 1 - 1, -t 1]

theorem hexagonalBrickFaces_adj (t : Site 2) :
    (hypercubicLattice 2).Adj
      (hexagonalBrickFaceLeft t) (hexagonalBrickFaceRight t) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp [hexagonalBrickFaceLeft, hexagonalBrickFaceRight]


theorem hexagonalBrickFaces_shared (t : Site 2) :
    sharedPrimalEdge (hexagonalBrickFaceLeft t)
        (hexagonalBrickFaceRight t) =
      s(hexagonalBrickVertex (t + hexagonalStep 1, true),
        hexagonalBrickVertex (t - hexagonalStep 1, false)) := by
  rw [show hexagonalBrickFaceRight t =
      hexagonalBrickFaceLeft t + ![1, 0] by
        ext k
        fin_cases k <;>
          simp [hexagonalBrickFaceLeft, hexagonalBrickFaceRight] <;> omega]
  unfold hexagonalBrickFaceLeft
  rw [show (![2 * t 0 + t 1 - 2, -t 1] : Site 2) + ![1, 0] =
      ![(2 * t 0 + t 1 - 2) + 1, -t 1] by
        ext k
        fin_cases k <;> simp]
  rw [sharedPrimalEdge_right]
  apply Sym2.eq_iff.mpr
  left
  constructor <;> ext k <;> fin_cases k <;>
    simp [faceCorner10, faceCorner11, hexagonalBrickVertex, hexagonalStep] <;>
    omega


theorem hexagonalBrickFaces_middle_not_adj (t : Site 2) :
    ¬ hexagonalGraph.Adj
      (t + hexagonalStep 1, true) (t - hexagonalStep 1, false) := by
  rw [hexagonalGraph_adj]
  intro hadj
  rcases hadj with hbad | h
  · simp at hbad
  rcases h with ⟨_, _, i, hi⟩
  fin_cases i <;>
    simp [hexagonalStep, funext_iff] at hi <;> omega


theorem triHexPlanarFiniteStar_middle_not_mem_imageGraph
    (n : Nat) (t : Site 2) :
    sharedPrimalEdge (hexagonalBrickFaceLeft t)
        (hexagonalBrickFaceRight t) ∉
      (imageGraph (triHexPlanarFiniteStarPlanar n)).edgeSet := by
  rw [hexagonalBrickFaces_shared, SimpleGraph.mem_edgeSet, imageGraph_adj]
  rintro ⟨u, v, huv, hu, hv⟩
  have hamb := triHexPlanarFiniteStarGraph_adj_hexagonal n huv
  have hu' : triHexPlanarFiniteStarVertexEmbedding n u =
      (t + hexagonalStep 1, true) := by
    apply hexagonalBrickVertex_injective
    exact hu
  have hv' : triHexPlanarFiniteStarVertexEmbedding n v =
      (t - hexagonalStep 1, false) := by
    apply hexagonalBrickVertex_injective
    exact hv
  rw [hu', hv'] at hamb
  exact hexagonalBrickFaces_middle_not_adj t hamb



theorem triHexPlanarFiniteStar_pfdFace_left_eq_right
    (n : Nat) (t : Site 2) :
    BeffaraDC.pfdFace (triHexPlanarFiniteStarPlanar n)
        (hexagonalBrickFaceLeft t) =
      BeffaraDC.pfdFace (triHexPlanarFiniteStarPlanar n)
        (hexagonalBrickFaceRight t) := by
  apply ConnectedComponent.connectedComponentMk_eq_of_adj
  rw [whb_faceRegion_adj]
  exact ⟨hexagonalBrickFaces_adj t,
    triHexPlanarFiniteStar_middle_not_mem_imageGraph n t⟩


noncomputable def triHexPlanarFiniteStarFace (n : Nat) (t : Site 2) :
    kwg_Face (triHexPlanarFiniteStarPlanar n) :=
  BeffaraDC.pfdFace (triHexPlanarFiniteStarPlanar n)
    (hexagonalBrickFaceLeft t)

theorem triHexPlanarFiniteStarFace_eq_right (n : Nat) (t : Site 2) :
    triHexPlanarFiniteStarFace n t =
      BeffaraDC.pfdFace (triHexPlanarFiniteStarPlanar n)
        (hexagonalBrickFaceRight t) :=
  triHexPlanarFiniteStar_pfdFace_left_eq_right n t




def triHexSpokeFace1 (z : Site 2) (i : Fin 3) : Site 2 :=
  ![z, z, z + hexagonalStep 0] i


def triHexSpokeFace2 (z : Site 2) (i : Fin 3) : Site 2 :=
  ![z + hexagonalStep 0, z + hexagonalStep 1,
    z + hexagonalStep 1] i


def triHexBrickSpokeFlank1 (z : Site 2) (i : Fin 3) : Site 2 :=
  ![hexagonalBrickFaceRight z,
    hexagonalBrickFaceRight z,
    hexagonalBrickFaceLeft (z + hexagonalStep 0)] i


def triHexBrickSpokeFlank2 (z : Site 2) (i : Fin 3) : Site 2 :=
  ![hexagonalBrickFaceLeft (z + hexagonalStep 0),
    hexagonalBrickFaceLeft (z + hexagonalStep 1),
    hexagonalBrickFaceRight (z + hexagonalStep 1)] i

theorem triHexBrickSpokeFlanks_adj (z : Site 2) (i : Fin 3) :
    (hypercubicLattice 2).Adj
      (triHexBrickSpokeFlank1 z i) (triHexBrickSpokeFlank2 z i) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  fin_cases i <;>
    simp [triHexBrickSpokeFlank1, triHexBrickSpokeFlank2,
      hexagonalBrickFaceLeft, hexagonalBrickFaceRight, hexagonalStep] <;>
    omega

theorem triHexBrickSpokeFlanks_shared (z : Site 2) (i : Fin 3) :
    sharedPrimalEdge (triHexBrickSpokeFlank1 z i)
        (triHexBrickSpokeFlank2 z i) =
      s(hexagonalBrickVertex (z, false),
        hexagonalBrickVertex (z + hexagonalStep i, true)) := by
  have hz : z = ![z 0, z 1] := by
    ext k
    fin_cases k <;> simp
  rw [hz]
  fin_cases i <;>
    simp [triHexBrickSpokeFlank1, triHexBrickSpokeFlank2,
      hexagonalBrickFaceLeft, hexagonalBrickFaceRight, hexagonalStep]
  all_goals ring_nf
  · rw [show (![z 0 * 2 + z 1, -z 1] : Site 2) =
        ![(-1 + z 0 * 2 + z 1) + 1, -z 1] by
          ext k; fin_cases k <;> simp <;> omega,
      sharedPrimalEdge_right]
    apply Sym2.eq_iff.mpr
    left
    constructor <;> ext k <;> fin_cases k <;>
      simp [faceCorner10, faceCorner11, hexagonalBrickVertex,
        hexagonalStep] <;> omega
  · rw [show (![-1 + z 0 * 2 + z 1, -1 - z 1] : Site 2) =
        ![-1 + z 0 * 2 + z 1, -z 1 - 1] by
          ext k; fin_cases k <;> simp <;> omega,
      sharedPrimalEdge_bottom]
    apply Sym2.eq_iff.mpr
    right
    constructor <;> ext k <;> fin_cases k <;>
      simp [faceCorner00, faceCorner10, hexagonalBrickVertex,
        hexagonalStep] <;> omega
  · rw [show (![z 0 * 2 + z 1, -1 - z 1] : Site 2) =
        ![z 0 * 2 + z 1, -z 1 - 1] by
          ext k; fin_cases k <;> simp <;> omega,
      sharedPrimalEdge_bottom]
    apply Sym2.eq_iff.mpr
    left
    constructor <;> ext k <;> fin_cases k <;>
      simp [faceCorner00, faceCorner10, hexagonalBrickVertex,
        hexagonalStep] <;> omega

theorem triHexBrickSpokeFlank1_face (n : Nat) (z : Site 2) (i : Fin 3) :
    BeffaraDC.pfdFace (triHexPlanarFiniteStarPlanar n)
        (triHexBrickSpokeFlank1 z i) =
      triHexPlanarFiniteStarFace n (triHexSpokeFace1 z i) := by
  fin_cases i
  · exact (triHexPlanarFiniteStarFace_eq_right n z).symm
  · exact (triHexPlanarFiniteStarFace_eq_right n z).symm
  · rfl

theorem triHexBrickSpokeFlank2_face (n : Nat) (z : Site 2) (i : Fin 3) :
    BeffaraDC.pfdFace (triHexPlanarFiniteStarPlanar n)
        (triHexBrickSpokeFlank2 z i) =
      triHexPlanarFiniteStarFace n (triHexSpokeFace2 z i) := by
  fin_cases i
  · rfl
  · rfl
  · exact (triHexPlanarFiniteStarFace_eq_right n
      (z + hexagonalStep 1)).symm

theorem triHexPlanarFiniteStar_embeddedEdge (n : Nat)
    (z : TriHexPlanarFiniteCell n) (i : Fin 3) :
    kwg_embeddedEdge (triHexPlanarFiniteStarPlanar n)
        (triHexPlanarFiniteStarEdgeEquiv n (z, i)) =
      s(hexagonalBrickVertex (z.1, false),
        hexagonalBrickVertex (z.1 + hexagonalStep i, true)) := by
  rfl

theorem triHexPlanarFiniteStar_embeddedEdge_mem_imageGraph (n : Nat)
    (z : TriHexPlanarFiniteCell n) (i : Fin 3) :
    kwg_embeddedEdge (triHexPlanarFiniteStarPlanar n)
        (triHexPlanarFiniteStarEdgeEquiv n (z, i)) ∈
      (imageGraph (triHexPlanarFiniteStarPlanar n)).edgeSet := by
  rw [triHexPlanarFiniteStar_embeddedEdge,
    SimpleGraph.mem_edgeSet, imageGraph_adj]
  refine ⟨Sum.inl z,
    Sum.inr (triHexPlanarFiniteTerminalMap n z i), ?_, rfl, ?_⟩
  · rw [← SimpleGraph.mem_edgeSet]
    exact (triHexPlanarFiniteStarEdgeEquiv n (z, i)).2
  · change hexagonalBrickVertex
      (triHexPlanarFiniteStarVertexEmbedding n
        (Sum.inr (triHexPlanarFiniteTerminalMap n z i))) = _
    congr 1

theorem triHexBrickSpokeFlanks_shared_mem_imageGraph (n : Nat)
    (z : TriHexPlanarFiniteCell n) (i : Fin 3) :
    sharedPrimalEdge (triHexBrickSpokeFlank1 z.1 i)
        (triHexBrickSpokeFlank2 z.1 i) ∈
      (imageGraph (triHexPlanarFiniteStarPlanar n)).edgeSet := by
  rw [triHexBrickSpokeFlanks_shared,
    ← triHexPlanarFiniteStar_embeddedEdge]
  exact triHexPlanarFiniteStar_embeddedEdge_mem_imageGraph n z i



theorem triHexPlanarFiniteStar_dualEnds (n : Nat)
    (z : TriHexPlanarFiniteCell n) (i : Fin 3) :
    kwg_dualEnds (triHexPlanarFiniteStarPlanar n)
        (triHexPlanarFiniteStarEdgeEquiv n (z, i)) =
      s(triHexPlanarFiniteStarFace n (triHexSpokeFace1 z.1 i),
        triHexPlanarFiniteStarFace n (triHexSpokeFace2 z.1 i)) := by
  let P := triHexPlanarFiniteStarPlanar n
  let e := triHexPlanarFiniteStarEdgeEquiv n (z, i)
  let f := triHexBrickSpokeFlank1 z.1 i
  let g := triHexBrickSpokeFlank2 z.1 i
  have hshared : sharedPrimalEdge f g = kwg_embeddedEdge P e := by
    dsimp only [f, g, P, e]
    rw [triHexBrickSpokeFlanks_shared,
      triHexPlanarFiniteStar_embeddedEdge]
  have hpair : s(kwg_flankLeft P e, kwg_flankRight P e) = s(f, g) :=
    (jce_sharedPrimalEdge_inj (kwg_flanks_adj P e)
      (triHexBrickSpokeFlanks_adj z.1 i)).mpr
        ((kwg_flanks_shared P e).trans hshared.symm)
  have hmapped :
      s((whb_faceRegion (imageGraph P)).connectedComponentMk
          (kwg_flankLeft P e),
        (whb_faceRegion (imageGraph P)).connectedComponentMk
          (kwg_flankRight P e)) =
      s((whb_faceRegion (imageGraph P)).connectedComponentMk f,
        (whb_faceRegion (imageGraph P)).connectedComponentMk g) := by
    simpa only [Sym2.map_mk] using congrArg
      (Sym2.map ((whb_faceRegion (imageGraph P)).connectedComponentMk)) hpair
  unfold kwg_dualEnds
  rw [hmapped]
  change s(BeffaraDC.pfdFace P f, BeffaraDC.pfdFace P g) = _
  rw [triHexBrickSpokeFlank1_face, triHexBrickSpokeFlank2_face]

end StatMech.FK.PeriodicPlanar

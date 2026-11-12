/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectLocalBoxEmbedding
import Code.FrontierD.FKRectStoppedPathTwoChannelAdapter
import Code.FrontierD.FKRectWindingBlockSource
import Code.Universality.RSWConnectorTwoChannelStoppedConditionalLaw










open SimpleGraph

namespace StatMech.FrontierD

open StatMech StatMech.Lattice
open StatMech.Universality

noncomputable section


def rlcConnectorFullRectangleGraph (scale : Nat) :
    SimpleGraph (RlcConnectorVertex (scale : Int)) where
  Adj x y := (hypercubicLattice 2).Adj (x : Site 2) (y : Site 2)
  symm := by
    intro x y hxy
    exact hxy.symm
  loopless := by
    constructor
    intro x hxx
    exact hxx.ne rfl

noncomputable instance rlcConnectorFullRectangleGraph_decidableAdj
    (scale : Nat) :
    DecidableRel (rlcConnectorFullRectangleGraph scale).Adj :=
  Classical.decRel _


theorem rlc_connectorFiniteGraph_le_fullRectangle
    (scale : Nat) (gamma : RlcRightDiagonalPath (scale : Int))
    (gamma' : RlcLeftDiagonalPath (scale : Int)) :
    rlc_connectorFiniteGraph gamma gamma' <=
      rlcConnectorFullRectangleGraph scale := by
  intro x y hxy
  exact hxy.1


theorem rlc_connectorTraceWiring_le_fullRectangle
    (scale : Nat) (gamma : RlcRightDiagonalPath (scale : Int))
    (gamma' : RlcLeftDiagonalPath (scale : Int)) :
    rlc_connectorTraceWiring gamma gamma' <=
      rlcConnectorFullRectangleGraph scale := by
  intro x y hxy
  exact hxy.1



theorem rlc_connectorTwoChannelGraph_le_fullRectangle
    (scale : Nat) (gamma : RlcRightDiagonalPath (scale : Int))
    (gamma' : RlcLeftDiagonalPath (scale : Int)) :
    rlc_connectorTwoChannelGraph gamma gamma' <=
      rlcConnectorFullRectangleGraph scale := by
  intro x y hxy
  exact hxy.1.elim (fun hcentral => hcentral.1)
    (fun hreflected => hreflected.1)



theorem rlc_twoChannelCompatibleExteriorFibre_fullRectangle
    (scale : Nat) (gamma : RlcRightDiagonalPath (scale : Int))
    (gamma' : RlcLeftDiagonalPath (scale : Int))
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex (scale : Int))))
    (htrace : ∀ e ∈
      (rlc_connectorTraceWiring gamma gamma').edgeFinset, psi e = true) :
    RlcTwoChannelCompatibleExteriorFibre gamma gamma'
      (rlcConnectorFullRectangleGraph scale) psi := by
  exact
    { twoChannel_le :=
        rlc_connectorTwoChannelGraph_le_fullRectangle scale gamma gamma'
      trace_le :=
        rlc_connectorTraceWiring_le_fullRectangle scale gamma gamma'
      trace_open := htrace }




theorem
    rlc_twoChannel_fullRectangle_bcProb_fibre_ge_of_retainedAnchor_staticCut
    (scale : Nat) (gamma : RlcRightDiagonalPath (scale : Int))
    (gamma' : RlcLeftDiagonalPath (scale : Int))
    (B : SimpleGraph (RlcConnectorVertex (scale : Int)))
    [DecidableRel B.Adj]
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex (scale : Int))))
    (htrace : ∀ e ∈
      (rlc_connectorTraceWiring gamma gamma').edgeFinset, psi e = true)
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hinc.1)
    {q : Real} (hq : 1 <= q) (N : Nat)
    (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect
      gamma gamma' N) :
    1 / (1 + (Real.sqrt q) ^ N * q) *
        (∑ rho ∈ FK.condFibre
          (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset psi,
          FK.bcProb (rlcConnectorFullRectangleGraph scale) B
            (BeffaraDC.selfDualPoint q) q rho) <=
      ∑ rho ∈ FK.condFibre
        (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset psi,
        (rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator
            (fun _ => (1 : Real)) rho *
          FK.bcProb (rlcConnectorFullRectangleGraph scale) B
            (BeffaraDC.selfDualPoint q) q rho := by
  exact
    StatMech.Universality.rlc_twoChannel_bcProb_fibre_ge_of_retainedAnchor_staticCut
      (rlcConnectorFullRectangleGraph scale) B psi
      (rlc_twoChannelCompatibleExteriorFibre_fullRectangle
        scale gamma gamma' psi htrace)
      hinc hstatic hq N hscore



theorem
    rlc_twoChannel_fullRectangle_bcProb_fibre_ge_of_retainedAnchor_staticCut_edgeCard
    (scale : Nat) (gamma : RlcRightDiagonalPath (scale : Int))
    (gamma' : RlcLeftDiagonalPath (scale : Int))
    (B : SimpleGraph (RlcConnectorVertex (scale : Int)))
    [DecidableRel B.Adj]
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex (scale : Int))))
    (htrace : ∀ e ∈
      (rlc_connectorTraceWiring gamma gamma').edgeFinset, psi e = true)
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hinc.1)
    {q : Real} (hq : 1 <= q) :
    let N := (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset.card + 2
    1 / (1 + (Real.sqrt q) ^ N * q) *
        (∑ rho ∈ FK.condFibre
          (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset psi,
          FK.bcProb (rlcConnectorFullRectangleGraph scale) B
            (BeffaraDC.selfDualPoint q) q rho) <=
      ∑ rho ∈ FK.condFibre
        (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset psi,
        (rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator
            (fun _ => (1 : Real)) rho *
          FK.bcProb (rlcConnectorFullRectangleGraph scale) B
            (BeffaraDC.selfDualPoint q) q rho := by
  dsimp only
  exact
    rlc_twoChannel_fullRectangle_bcProb_fibre_ge_of_retainedAnchor_staticCut
      scale gamma gamma' B psi htrace hinc hstatic hq _
        (rlc_twoChannelFullPhysicalPermutationScoreDefect_edgeCard_add_two
          gamma gamma')




theorem
    rlc_twoChannel_fullRectangleOutsideEventMass_lower_of_retainedAnchor_staticCut
    (scale : Nat) (gamma : RlcRightDiagonalPath (scale : Int))
    (gamma' : RlcLeftDiagonalPath (scale : Int))
    (B : SimpleGraph (RlcConnectorVertex (scale : Int)))
    [DecidableRel B.Adj]
    (S : Set (ConfigSpace (Sym2 (RlcConnectorVertex (scale : Int)))))
    (hS : FK.DependsOnOutside
      (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset S)
    (htrace : ∀ {psi}, psi ∈ S → ∀ e ∈
      (rlc_connectorTraceWiring gamma gamma').edgeFinset, psi e = true)
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hinc.1)
    {q : Real} (hq : 1 <= q) (N : Nat)
    (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect
      gamma gamma' N) :
    1 / (1 + (Real.sqrt q) ^ N * q) *
        (∑ rho, S.indicator (fun _ => (1 : Real)) rho *
          FK.bcProb (rlcConnectorFullRectangleGraph scale) B
            (BeffaraDC.selfDualPoint q) q rho) <=
      ∑ rho,
        (rlc_finiteTwoChannelConnectorEvent gamma gamma' ∩ S).indicator
            (fun _ => (1 : Real)) rho *
          FK.bcProb (rlcConnectorFullRectangleGraph scale) B
            (BeffaraDC.selfDualPoint q) q rho := by
  exact
    StatMech.Universality.rlc_twoChannelOutsideEventMass_lower_of_retainedAnchor_staticCut
      gamma gamma' (rlcConnectorFullRectangleGraph scale) B S hS
      (fun {psi} hpsi =>
        rlc_twoChannelCompatibleExteriorFibre_fullRectangle
          scale gamma gamma' psi (htrace hpsi))
      hinc hstatic hq N hscore



theorem
    rlc_twoChannel_fullRectangleOutsideEventMass_lower_of_retainedAnchor_staticCut_edgeCard
    (scale : Nat) (gamma : RlcRightDiagonalPath (scale : Int))
    (gamma' : RlcLeftDiagonalPath (scale : Int))
    (B : SimpleGraph (RlcConnectorVertex (scale : Int)))
    [DecidableRel B.Adj]
    (S : Set (ConfigSpace (Sym2 (RlcConnectorVertex (scale : Int)))))
    (hS : FK.DependsOnOutside
      (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset S)
    (htrace : ∀ {psi}, psi ∈ S → ∀ e ∈
      (rlc_connectorTraceWiring gamma gamma').edgeFinset, psi e = true)
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hinc.1)
    {q : Real} (hq : 1 <= q) :
    let N := (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset.card + 2
    1 / (1 + (Real.sqrt q) ^ N * q) *
        (∑ rho, S.indicator (fun _ => (1 : Real)) rho *
          FK.bcProb (rlcConnectorFullRectangleGraph scale) B
            (BeffaraDC.selfDualPoint q) q rho) <=
      ∑ rho,
        (rlc_finiteTwoChannelConnectorEvent gamma gamma' ∩ S).indicator
            (fun _ => (1 : Real)) rho *
          FK.bcProb (rlcConnectorFullRectangleGraph scale) B
            (BeffaraDC.selfDualPoint q) q rho := by
  dsimp only
  exact
    rlc_twoChannel_fullRectangleOutsideEventMass_lower_of_retainedAnchor_staticCut
      scale gamma gamma' B S hS htrace hinc hstatic hq _
        (rlc_twoChannelFullPhysicalPermutationScoreDefect_edgeCard_add_two
          gamma gamma')




theorem
    rlc_finiteExtremalPairCandidate_fullRectangle_twoChannelMass_lower_edgeCard
    (scale : Nat) (gamma : RlcRightDiagonalPath (scale : Int))
    (gamma' : RlcLeftDiagonalPath (scale : Int))
    (B : SimpleGraph (RlcConnectorVertex (scale : Int)))
    [DecidableRel B.Adj]
    (hdisj : Disjoint
      (rlc_finiteExtremalPairCandidateEdges gamma gamma')
      (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset)
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hinc.1)
    {q : Real} (hq : 1 <= q) :
    let N := (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset.card + 2
    1 / (1 + (Real.sqrt q) ^ N * q) *
        (∑ rho,
          (rlc_finiteExtremalPairCandidate gamma gamma').indicator
              (fun _ => (1 : Real)) rho *
            FK.bcProb (rlcConnectorFullRectangleGraph scale) B
              (BeffaraDC.selfDualPoint q) q rho) <=
      ∑ rho,
        (rlc_finiteTwoChannelConnectorEvent gamma gamma' ∩
            rlc_finiteExtremalPairCandidate gamma gamma').indicator
              (fun _ => (1 : Real)) rho *
          FK.bcProb (rlcConnectorFullRectangleGraph scale) B
            (BeffaraDC.selfDualPoint q) q rho := by
  dsimp only
  exact
    rlc_finiteExtremalPairCandidate_twoChannelMass_lower_of_retainedAnchor_staticCut
      gamma gamma' (rlcConnectorFullRectangleGraph scale) B
      (rlc_connectorTwoChannelGraph_le_fullRectangle scale gamma gamma')
      (rlc_connectorTraceWiring_le_fullRectangle scale gamma gamma')
      hdisj hinc hstatic hq _
        (rlc_twoChannelFullPhysicalPermutationScoreDefect_edgeCard_add_two
          gamma gamma')



def rlcConnectorFullRectangleBoxInclusion (scale : Nat) :
    RlcConnectorVertex (scale : Int) -> FK.boxVerts 2 (2 * scale) :=
  fun z => ⟨z, by
    have hzRect := z.2
    change z.1 ∈ StatMech.RSW.Box.rect
      (-2 * (scale : Int)) (2 * (scale : Int))
      (-(scale : Int)) (scale : Int) at hzRect
    rw [StatMech.RSW.Box.mem_rect] at hzRect
    rw [mem_box]
    intro i
    fin_cases i <;> simp at hzRect ⊢ <;> omega⟩

theorem rlcConnectorFullRectangleBoxInclusion_injective (scale : Nat) :
    Function.Injective (rlcConnectorFullRectangleBoxInclusion scale) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg
    (fun z : FK.boxVerts 2 (2 * scale) => (z : Site 2)) hxy

theorem rlcConnectorFullRectangleBoxInclusion_adjMatch (scale : Nat) :
    FK.ocd_AdjMatch (rlcConnectorFullRectangleGraph scale)
      (FK.boxGraph 2 (2 * scale))
      (rlcConnectorFullRectangleBoxInclusion scale) := by
  intro x y
  rfl


def fkRectStoppedPathFullRectangleEmbedding
    (R : FKRectTorus) (center : R.Vertex)
    (scale cut lower upper : Nat)
    (hfit : FKRectLocalBoxFits R center (2 * scale) cut lower upper) :
    RlcConnectorVertex (scale : Int) -> R.Vertex :=
  fun z =>
    (fkRectLocalBoxEmbedding R center (2 * scale) cut lower upper hfit
      (rlcConnectorFullRectangleBoxInclusion scale z)).1

theorem fkRectStoppedPathFullRectangleEmbedding_injective
    (R : FKRectTorus) (center : R.Vertex)
    (scale cut lower upper : Nat)
    (hfit : FKRectLocalBoxFits R center (2 * scale) cut lower upper) :
    Function.Injective
      (fkRectStoppedPathFullRectangleEmbedding
        R center scale cut lower upper hfit) := by
  intro x y hxy
  apply rlcConnectorFullRectangleBoxInclusion_injective scale
  apply fkRectLocalBoxEmbedding_injective
    R center (2 * scale) cut lower upper hfit
  apply Subtype.ext
  exact hxy


theorem fkRectStoppedPathFullRectangleEmbedding_adjMatch
    (R : FKRectTorus) (center : R.Vertex)
    (scale cut lower upper : Nat)
    (hcut : 1 <= cut) (hlower : 1 <= lower)
    (hfit : FKRectLocalBoxFits R center (2 * scale) cut lower upper) :
    FK.ocd_AdjMatch (rlcConnectorFullRectangleGraph scale)
      (fkRectTorusGraph R)
      (fkRectStoppedPathFullRectangleEmbedding
        R center scale cut lower upper hfit) := by
  let incl := rlcConnectorFullRectangleBoxInclusion scale
  let emb := fkRectLocalBoxEmbedding
    R center (2 * scale) cut lower upper hfit
  have hbox := fkRectLocalBoxEmbedding_adjMatch
    R center (2 * scale) cut lower upper hcut hlower hfit
  intro x y
  exact (rlcConnectorFullRectangleBoxInclusion_adjMatch scale x y).trans
    (by
      change (FK.boxGraph 2 (2 * scale)).Adj (incl x) (incl y) ↔
        (fkRectTorusGraph R).Adj (emb (incl x)).1 (emb (incl y)).1
      exact hbox (incl x) (incl y))



def fkRectWindingStoppedRectangleCenter
    (k scale blocks : Nat)
    (hwidth : 12 * scale + 2 < 2 * (k + 3))
    (hblocks : 3 <= blocks) :
    (fkRectWindingBlockVerticalFamily k scale blocks).Vertex :=
  (⟨4 * scale + 1, by
    simp only [fkRectWindingBlockVerticalFamily_width]
    omega⟩, ⟨4 * scale + 1, by
    simp only [fkRectWindingBlockVerticalFamily_height]
    nlinarith⟩)



theorem fkRectWindingStoppedRectangle_fits
    (k scale blocks : Nat)
    (hwidth : 12 * scale + 2 < 2 * (k + 3))
    (hblocks : 3 <= blocks) :
    FKRectLocalBoxFits
      (fkRectWindingBlockVerticalFamily k scale blocks)
      (fkRectWindingStoppedRectangleCenter
        k scale blocks hwidth hblocks)
      (2 * scale) 1 1
      ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1) := by
  apply fkRectLocalBoxFits_of_margin
  · exact Nat.sub_lt
      (fkRectWindingBlockVerticalFamily k scale blocks).height_pos
      (by omega)
  · change 1 + 2 * (2 * scale) <= 4 * scale + 1
    omega
  · change 4 * scale + 1 + 2 * (2 * scale) < 2 * (k + 3)
    omega
  · change 1 + 2 * (2 * scale) <= 4 * scale + 1
    omega
  · change 4 * scale + 1 + 2 * (2 * scale) <=
      (fkRectWindingBlockVerticalFamily k scale blocks).height - 1
    simp only [fkRectWindingBlockVerticalFamily_height]
    have hmul : (scale + 1) * 4 <= (scale + 1) * (blocks + 1) :=
      Nat.mul_le_mul_left (scale + 1) (by omega)
    rw [Nat.mul_assoc]
    omega



def fkRectWindingStoppedRectangleEmbedding
    (k scale blocks : Nat)
    (hwidth : 12 * scale + 2 < 2 * (k + 3))
    (hblocks : 3 <= blocks) :
    RlcConnectorVertex (scale : Int) ->
      (fkRectWindingBlockVerticalFamily k scale blocks).Vertex :=
  fkRectStoppedPathFullRectangleEmbedding
    (fkRectWindingBlockVerticalFamily k scale blocks)
    (fkRectWindingStoppedRectangleCenter
      k scale blocks hwidth hblocks)
    scale 1 1
    ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)
    (fkRectWindingStoppedRectangle_fits
      k scale blocks hwidth hblocks)

theorem fkRectWindingStoppedRectangleEmbedding_injective
    (k scale blocks : Nat)
    (hwidth : 12 * scale + 2 < 2 * (k + 3))
    (hblocks : 3 <= blocks) :
    Function.Injective
      (fkRectWindingStoppedRectangleEmbedding
        k scale blocks hwidth hblocks) :=
  fkRectStoppedPathFullRectangleEmbedding_injective
    (fkRectWindingBlockVerticalFamily k scale blocks)
    (fkRectWindingStoppedRectangleCenter
      k scale blocks hwidth hblocks)
    scale 1 1
    ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)
    (fkRectWindingStoppedRectangle_fits
      k scale blocks hwidth hblocks)

theorem fkRectWindingStoppedRectangleEmbedding_adjMatch
    (k scale blocks : Nat)
    (hwidth : 12 * scale + 2 < 2 * (k + 3))
    (hblocks : 3 <= blocks) :
    FK.ocd_AdjMatch (rlcConnectorFullRectangleGraph scale)
      (fkRectTorusGraph
        (fkRectWindingBlockVerticalFamily k scale blocks))
      (fkRectWindingStoppedRectangleEmbedding
        k scale blocks hwidth hblocks) :=
  fkRectStoppedPathFullRectangleEmbedding_adjMatch
    (fkRectWindingBlockVerticalFamily k scale blocks)
    (fkRectWindingStoppedRectangleCenter
      k scale blocks hwidth hblocks)
    scale 1 1
    ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)
    (by omega) (by omega)
    (fkRectWindingStoppedRectangle_fits
      k scale blocks hwidth hblocks)







theorem fkRectWinding_bookFaithfulStoppedPair_fibre_lower
    (k scale blocks : Nat)
    (hwidth : 12 * scale + 2 < 2 * (k + 3))
    (hblocks : 3 <= blocks)
    (gamma : RlcRightDiagonalPath (scale : Int))
    (gamma' : RlcLeftDiagonalPath (scale : Int))
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (psi : ConfigSpace (Sym2
      (fkRectWindingBlockVerticalFamily k scale blocks).Vertex))
    (C : SimpleGraph (RlcConnectorVertex (scale : Int)))
    [DecidableRel C.Adj]
    (hC : FK.ocd_inducedWiring
      (fkRectTorusGraph
        (fkRectWindingBlockVerticalFamily k scale blocks))
      (fkRectWindingStoppedRectangleEmbedding
        k scale blocks hwidth hblocks)
      (fun _ => False) psi = C)
    {q c : Real} (hq : 1 <= q)
    (hc : c <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
      (rlc_connectorSeparateWiring gamma gamma')
      (BeffaraDC.selfDualPoint q) q
      (rlc_finiteConnectorEvent gamma gamma')) :
    let iota := fkRectWindingStoppedRectangleEmbedding
      k scale blocks hwidth hblocks
    let G := fkRectTorusGraph
      (fkRectWindingBlockVerticalFamily k scale blocks)
    let F := FK.ocd_innerEdgeFinset iota
    c *
        (∑ rho ∈ FK.condFibre F psi,
          (FK.ocd_innerRestrict iota ⁻¹'
            rlc_finiteExtremalPairCandidate gamma gamma').indicator
              (fun _ => (1 : Real)) rho *
            FK.fkProb G (fkRectCriticalP q) q rho) <=
      ∑ rho ∈ FK.condFibre F psi,
        (FK.ocd_innerRestrict iota ⁻¹'
          (rlc_finiteConnectorEvent gamma gamma' ∩
            rlc_finiteExtremalPairCandidate gamma gamma')).indicator
              (fun _ => (1 : Real)) rho *
          FK.fkProb G (fkRectCriticalP q) q rho := by
  classical
  let R := fkRectWindingBlockVerticalFamily k scale blocks
  let iota := fkRectWindingStoppedRectangleEmbedding
    k scale blocks hwidth hblocks
  let G := fkRectTorusGraph R
  have hraw := rlc_bookFaithfulStoppedPair_bcProb_outerFibre_lower
    (Gout := G) (bdryOut := fun _ : R.Vertex => False)
    hfaith (rlcConnectorFullRectangleGraph scale)
    (rlc_connectorFiniteGraph_le_fullRectangle scale gamma gamma')
    (rlc_connectorTraceWiring_le_fullRectangle scale gamma gamma')
    iota
    (fkRectWindingStoppedRectangleEmbedding_injective
      k scale blocks hwidth hblocks)
    (fkRectWindingStoppedRectangleEmbedding_adjMatch
      k scale blocks hwidth hblocks)
    psi C hC hq hc
  have hboundary : boundaryCliqueGraph (fun _ : R.Vertex => False) =
      (⊥ : SimpleGraph R.Vertex) := by
    apply SimpleGraph.ext
    ext x y
    rw [boundaryCliqueGraph_adj]
    simp [SimpleGraph.bot_adj]
  dsimp only
  simpa only [R, iota, G, hboundary, FK.bcProb_bot_eq_fkProb,
    fkRectCriticalP, BeffaraDC.selfDualPoint] using hraw


theorem fkRectWinding_bookFaithfulStoppedPair_fibre_qsq_lower
    (k scale blocks : Nat)
    (hwidth : 12 * scale + 2 < 2 * (k + 3))
    (hblocks : 3 <= blocks)
    (gamma : RlcRightDiagonalPath (scale : Int))
    (gamma' : RlcLeftDiagonalPath (scale : Int))
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (psi : ConfigSpace (Sym2
      (fkRectWindingBlockVerticalFamily k scale blocks).Vertex))
    (C : SimpleGraph (RlcConnectorVertex (scale : Int)))
    [DecidableRel C.Adj]
    (hC : FK.ocd_inducedWiring
      (fkRectTorusGraph
        (fkRectWindingBlockVerticalFamily k scale blocks))
      (fkRectWindingStoppedRectangleEmbedding
        k scale blocks hwidth hblocks)
      (fun _ => False) psi = C)
    {q : Real} (hq : 1 <= q)
    (hlocal : 1 / (1 + q ^ 2) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma')) :
    let iota := fkRectWindingStoppedRectangleEmbedding
      k scale blocks hwidth hblocks
    let G := fkRectTorusGraph
      (fkRectWindingBlockVerticalFamily k scale blocks)
    let F := FK.ocd_innerEdgeFinset iota
    1 / (1 + q ^ 2) *
        (∑ rho ∈ FK.condFibre F psi,
          (FK.ocd_innerRestrict iota ⁻¹'
            rlc_finiteExtremalPairCandidate gamma gamma').indicator
              (fun _ => (1 : Real)) rho *
            FK.fkProb G (fkRectCriticalP q) q rho) <=
      ∑ rho ∈ FK.condFibre F psi,
        (FK.ocd_innerRestrict iota ⁻¹'
          (rlc_finiteConnectorEvent gamma gamma' ∩
            rlc_finiteExtremalPairCandidate gamma gamma')).indicator
              (fun _ => (1 : Real)) rho *
          FK.fkProb G (fkRectCriticalP q) q rho := by
  exact fkRectWinding_bookFaithfulStoppedPair_fibre_lower
    k scale blocks hwidth hblocks gamma gamma' hfaith psi C hC hq hlocal

end

end StatMech.FrontierD

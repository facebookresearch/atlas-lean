/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBarrierRightStrip



namespace StatMech.FrontierD

noncomputable section



def fkRectRightBandBarrierConnectionEvent
    (R : FKRectTorus) (leftRight cut lower upper : Nat)
    (I : Finset R.EdgeIndex) (eta : R.Configuration)
    (t : Finset (FKRectRightStripBandVertex R cut lower upper ×
      FKRectRightStripBandVertex R cut lower upper)) :
    Set (ConfigSpace (Sym2 R.Vertex)) :=
  (FK.ocd_innerRestrict
      (Subtype.val :
        FKRectRightStripBandVertex R cut lower upper → R.Vertex) ⁻¹'
        fkRectInducedConnectionChainEvent R
          (fkRectRightStripBand R cut lower upper) t) ∩
    fkRectFullGraphEvent R
      (fkRectLeftBarrierWithSeamPattern R leftRight I eta)



theorem fkRectRightBand_barrierConnectionProduct_le
    (R : FKRectTorus)
    (leftRight cut lower upper : Nat)
    (hsep : leftRight < cut) (hlower : 1 ≤ lower)
    {q : Real} (hq : 1 ≤ q)
    (I : Finset R.EdgeIndex)
    (hI : ∀ a ∈ I,
      fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R a))
    (eta : R.Configuration)
    (t : Finset (FKRectRightStripBandVertex R cut lower upper ×
      FKRectRightStripBandVertex R cut lower upper)) :
    (∏ xy ∈ t,
        FK.twoPointFun
          (fkRectInducedGraph R
            (fkRectRightStripBand R cut lower upper))
          (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q
          (fkRectLeftBarrierWithSeamPattern R leftRight I eta) ≤
      ∑ rho,
        (fkRectRightBandBarrierConnectionEvent R
          leftRight cut lower upper I eta t).indicator
            (fun _ => (1 : Real)) rho *
          FK.fkProb (fkRectTorusGraph R)
            (fkRectCriticalP q) q rho := by
  exact fkRectRightStripBand_connectionProduct_mul_outsideMass_le_genericInter
    R cut lower upper hq t
      (fkRectLeftBarrierWithSeamPattern_dependsOnOutsideRightStripBand
        R leftRight cut lower upper hsep hlower I hI eta)

end

end StatMech.FrontierD

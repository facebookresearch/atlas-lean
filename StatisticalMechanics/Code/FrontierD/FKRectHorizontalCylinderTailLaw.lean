/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectHorizontalCylinderAdaptiveStep









namespace StatMech.FrontierD

noncomputable section



theorem fkRectHorizontalCylinderCrossingClusterCount_congr_openSub
    (R : FKRectTorus) {rho sigma : ConfigSpace (Sym2 R.Vertex)}
    (hgraph :
      FK.openSub (fkRectHorizontalCylinderGraph R) rho =
        FK.openSub (fkRectHorizontalCylinderGraph R) sigma) :
    fkRectHorizontalCylinderCrossingClusterCount R rho =
      fkRectHorizontalCylinderCrossingClusterCount R sigma := by
  classical
  let G := FK.openSub (fkRectHorizontalCylinderGraph R) rho
  let H := FK.openSub (fkRectHorizontalCylinderGraph R) sigma
  have hrel : forall {x y : R.Vertex}, H.Adj x y <-> G.Adj x y := by
    intro x y
    change (FK.openSub (fkRectHorizontalCylinderGraph R) sigma).Adj x y <->
      (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Adj x y
    rw [hgraph]
  let phi : G ≃g H := ⟨Equiv.refl R.Vertex, hrel⟩
  let e : G.ConnectedComponent ≃ H.ConnectedComponent :=
    phi.connectedComponentEquiv
  unfold fkRectHorizontalCylinderCrossingClusterCount
  apply Fintype.card_congr
  refine Equiv.subtypeEquiv e ?_
  intro C
  change FKRectHorizontalCylinderCrossingComponent R rho C <->
    FKRectHorizontalCylinderCrossingComponent R sigma (e C)
  unfold FKRectHorizontalCylinderCrossingComponent
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨⟨x, ?_⟩, ⟨y, ?_⟩⟩
    · calc
        H.connectedComponentMk (x, fkRectBottomRow R) =
            e (G.connectedComponentMk (x, fkRectBottomRow R)) := by
              simp [e, phi]
        _ = e C := congrArg e hx
    · calc
        H.connectedComponentMk (y, fkRectTopRow R) =
            e (G.connectedComponentMk (y, fkRectTopRow R)) := by
              simp [e, phi]
        _ = e C := congrArg e hy
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨⟨x, ?_⟩, ⟨y, ?_⟩⟩
    · apply e.injective
      simpa [e, phi] using hx
    · apply e.injective
      simpa [e, phi] using hy




theorem fkRectHorizontalCylinderCrossingTail_edgeEvent_eq
    (R : FKRectTorus) (n : Nat) :
    FK.ecz_closeOff (fkRectHorizontalCylinderGraph R) ⁻¹'
        fkRectHorizontalCylinderEdgeEvent R
          {eta | n <= fkRectHorizontalCutPrimalCrossingClusterCount R
            (fkRectForceHorizontalCutClosed R eta)} =
      {rho | n <= fkRectHorizontalCylinderCrossingClusterCount R rho} := by
  ext rho
  let sigma := FK.ecz_closeOff (fkRectHorizontalCylinderGraph R) rho
  let eta :=
    (fkRectHorizontalCutClosedEdgeConfigEquiv R).symm sigma
  change n <= fkRectHorizontalCutPrimalCrossingClusterCount R
      (fkRectForceHorizontalCutClosed R eta.1) <-> _
  have hclosed : fkRectForceHorizontalCutClosed R eta.1 = eta.1 :=
    fkRectHorizontalCutClosedConfiguration_force_eq_self R eta.1 eta.2
  rw [hclosed]
  have hequiv : fkRectHorizontalCutClosedEdgeConfigEquiv R eta = sigma :=
    (fkRectHorizontalCutClosedEdgeConfigEquiv R).apply_symm_apply sigma
  rw [<- fkRectHorizontalCylinderCrossingClusterCount_eq_horizontalCut R eta]
  have hval :
      (fkRectHorizontalCutClosedEdgeConfigEquiv R eta).1 = sigma.1 :=
    congrArg Subtype.val hequiv
  rw [hval]
  rw [fkRectHorizontalCylinderCrossingClusterCount_congr_openSub R
    (openSub_ecz_closeOff_horizontalCylinder R rho)]
  rfl



theorem fkRectCriticalHorizontalCut_crossingTail_eq_finiteEventMass
    (R : FKRectTorus) {q : Real} (hq : 1 <= q) (n : Nat) :
    fkRectCriticalHorizontalCutEventMass R q
        {eta | n <= fkRectHorizontalCutPrimalCrossingClusterCount R
          (fkRectForceHorizontalCutClosed R eta)} =
      StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectHorizontalCylinderGraph R)
          (fkRectCriticalP q) q)
        {rho | n <= fkRectHorizontalCylinderCrossingClusterCount R rho} := by
  rw [fkRectCriticalHorizontalCutEventMass_eq_cylinderGraph R hq,
    fkRectHorizontalCylinderCrossingTail_edgeEvent_eq]
  unfold StatMech.Probability.finiteEventMass
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hmem : n <= fkRectHorizontalCylinderCrossingClusterCount R rho <;>
    simp [Set.indicator, hmem]



theorem fkRectCriticalHorizontalCut_crossingTail_le_pow_pred_of_twoPoint
    (R : FKRectTorus) {q a : Real} (hq : 1 <= q) (ha : 0 <= a)
    (htwo : forall (pair : Fin R.width -> Fin R.width)
        (T : Finset (Fin R.width)) (hT : T.Nonempty)
        (x : Fin R.width) (hx : x ∉ T)
        (psi : ConfigSpace (Sym2 R.Vertex))
        (hbase : FKRectHorizontalCylinderDistinctPairedWitness R pair T psi)
        (hsource : ¬ FKRectHorizontalCylinderExploredVertex R psi T
          (x, fkRectBottomRow R))
        (htarget : ¬ FKRectHorizontalCylinderExploredVertex R psi T
          (pair x, fkRectTopRow R)),
      FK.infiniteTwoPointReal
        (FK.freeInfiniteVolume 2
          (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
          (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
          (zero_lt_one.trans_le hq) :
            MeasureTheory.Measure
              (ConfigSpace (Sym2 (StatMech.Lattice.Site 2))))
        ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness
            R psi pair T hT hbase).embedding
          ⟨(x, fkRectBottomRow R), hsource⟩).1
        ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness
            R psi pair T hT hbase).embedding
          ⟨(pair x, fkRectTopRow R), htarget⟩).1 <= a)
    (n : Nat) (hn : 0 < n) :
    fkRectCriticalHorizontalCutEventMass R q
        {eta | n <= fkRectHorizontalCutPrimalCrossingClusterCount R
          (fkRectForceHorizontalCutClosed R eta)} <=
      Nat.choose R.width n * R.width ^ R.width * a ^ (n - 1) := by
  rw [fkRectCriticalHorizontalCut_crossingTail_eq_finiteEventMass R hq n]
  exact fkRectHorizontalCylinderCrossingTail_le_pow_pred_of_twoPoint R
    (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
    (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
    hq ha htwo n hn

end

end StatMech.FrontierD

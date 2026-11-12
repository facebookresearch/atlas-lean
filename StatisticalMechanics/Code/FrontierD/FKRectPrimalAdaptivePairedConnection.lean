/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectPrimalAdaptiveProjection
import Code.FrontierD.FKRectPrimalPairedConnection









open MeasureTheory SimpleGraph StatMech.Lattice

namespace StatMech.FrontierD

noncomputable section

private instance instDecidableFalseBoundaryAdaptivePaired (R : FKRectTorus) :
    DecidablePred (fun _ : R.Vertex => False) :=
  fun _ => isFalse id



theorem fkRectPrimalAdaptive_condMass_eq_freeUnexplored
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (psi : ConfigSpace (Sym2 R.Vertex))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2
      (FKRectPrimalUnexploredVertex R S (fkRectCutConfigOfFull R psi).1)))) :
    (∑ rho : ConfigSpace (Sym2 R.Vertex),
        (FK.ocd_innerRestrict
          (Subtype.val : FKRectPrimalUnexploredVertex R S
            (fkRectCutConfigOfFull R psi).1 -> R.Vertex) ⁻¹' A).indicator
              (fun _ => (1 : Real)) rho *
          FK.condBcProb (fkRectCutGraph R)
            (boundaryCliqueGraph (fun _ : R.Vertex => False)) p q
            (fkRectPrimalAdaptiveInsideEdges R S psi) psi rho) =
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        FK.fkProb (fkRectPrimalUnexploredInducedGraph R S
          (fkRectCutConfigOfFull R psi).1) p q omega := by
  let eta := fkRectCutConfigOfFull R psi
  let iota :=
    (Subtype.val : FKRectPrimalUnexploredVertex R S eta.1 -> R.Vertex)
  let psi0 := fkRectFullGraphConfiguration R eta.1
  have hforce : fkRectForceCutClosed R eta.1 = eta.1 := eta.2
  have hbot0 := fkRectPrimalExploration_ocdInducedWiring_eq_bot R S eta.1
  rw [hforce] at hbot0
  have hedgeEq : forall x y : R.Vertex, (fkRectCutGraph R).Adj x y ->
      psi s(x, y) = psi0 s(x, y) := by
    intro x y hxy
    have hedge : s(x, y) ∈ (fkRectCutGraph R).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset]
      exact hxy
    have hclose := FK.ecz_closeOff_apply_edge (fkRectCutGraph R) psi hedge
    change psi s(x, y) =
      fkRectFullGraphConfiguration R (fkRectCutConfigOfFull R psi).1 s(x, y)
    rw [fkRectFullGraphConfiguration_cutConfigOfFull R psi]
    exact hclose.symm
  have hwiring :
      FK.ocd_inducedWiring (fkRectCutGraph R) iota
          (fun _ : R.Vertex => False) psi =
        (⊥ : SimpleGraph (FKRectPrimalUnexploredVertex R S eta.1)) := by
    exact (FK.ocd_inducedWiring_congr_edges
      (fkRectCutGraph R) iota (fun _ : R.Vertex => False)
      psi psi0 hedgeEq).trans hbot0
  have hevent := FK.ocd_condBcProb_innerEvent_eq_of_psiExt
    (Gin := fkRectPrimalUnexploredInducedGraph R S eta.1)
    (Gout := fkRectCutGraph R)
    (iota := iota) (bdryOut := fun _ : R.Vertex => False)
    Subtype.val_injective
    (fkRectPrimalUnexploredInducedGraph_adjMatch R S eta.1)
    hp hp1 hq psi
    (fun omega => FK.fkProb
      (fkRectPrimalUnexploredInducedGraph R S eta.1) p q omega)
    (fun omega => by
      have hdm := FK.ocd_condBcProb_psiExt_eq_bcProb
        (Gin := fkRectPrimalUnexploredInducedGraph R S eta.1)
        (Gout := fkRectCutGraph R)
        (ιV := iota) (bdryOut := fun _ : R.Vertex => False)
        Subtype.val_injective
        (fkRectPrimalUnexploredInducedGraph_adjMatch R S eta.1)
        hp hp1 hq psi omega
      have hfree := @FK.bcProb_congr_boundary
        (FKRectPrimalUnexploredVertex R S eta.1)
        (instFintypeFKRectPrimalUnexploredVertex R S eta.1)
        (instDecidableEqFKRectPrimalUnexploredVertex R S eta.1)
        (fkRectPrimalUnexploredInducedGraph R S eta.1)
        (FK.ocd_inducedWiring (fkRectCutGraph R) iota
          (fun _ : R.Vertex => False) psi)
        (⊥ : SimpleGraph (FKRectPrimalUnexploredVertex R S eta.1))
        (instDecidableRelPrimalUnexploredInducedGraph R S eta.1)
        (FK.instDecidableRelAdjOcd_inducedWiring _ _ _)
        (by infer_instance) hwiring p q omega
      rw [FK.bcProb_bot_eq_fkProb] at hfree
      exact hdm.trans hfree)
    A
  have hF : fkRectPrimalAdaptiveInsideEdges R S psi =
      fkRectPrimalUnexploredPairEdges R S eta.1 :=
    fkRectPrimalFullUnexploredPairEdges_eq_decoded R S psi
  rw [hF]
  simpa only [eta, iota] using hevent



def FKRectPrimalAdaptivePairedConnectionEvent
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (i targetRow : Fin R.height) (psi : ConfigSpace (Sym2 R.Vertex)) :
    Set (ConfigSpace (Sym2 R.Vertex)) :=
  {rho | ∃ hsource : ¬ FKRectPrimalFullExploredVertex R S psi
      (fkRectLeftColumn R, i),
    ∃ htarget : ¬ FKRectPrimalFullExploredVertex R S psi
      (fkRectRightColumn R, targetRow),
    let source : FKRectPrimalUnexploredVertex R S
        (fkRectCutConfigOfFull R psi).1 :=
      ⟨(fkRectLeftColumn R, i), fun h => hsource
        ((fkRectPrimalFullExploredVertex_iff R S psi _).2 h)⟩
    let target : FKRectPrimalUnexploredVertex R S
        (fkRectCutConfigOfFull R psi).1 :=
      ⟨(fkRectRightColumn R, targetRow), fun h => htarget
        ((fkRectPrimalFullExploredVertex_iff R S psi _).2 h)⟩
    FK.ocd_innerRestrict
        (Subtype.val : FKRectPrimalUnexploredVertex R S
          (fkRectCutConfigOfFull R psi).1 -> R.Vertex) rho ∈
      FKRectPrimalUnexploredConnectionEvent R S
        (fkRectCutConfigOfFull R psi).1 source target}


theorem fkRectPrimalAdaptivePairedConnectionEvent_condMass_le_boxConn
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (i targetRow : Fin R.height) (psi : ConfigSpace (Sym2 R.Vertex))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    (∑ rho : ConfigSpace (Sym2 R.Vertex),
        (FKRectPrimalAdaptivePairedConnectionEvent
          R S i targetRow psi).indicator (fun _ => (1 : Real)) rho *
          FK.condBcProb (fkRectCutGraph R)
            (boundaryCliqueGraph (fun _ : R.Vertex => False)) p q
            (fkRectPrimalAdaptiveInsideEdges R S psi) psi rho) <=
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (FK.boxConnEvent 2 (R.width + R.height)
            (fkRectVertexBoxEmbedding R (fkRectLeftColumn R, i))
            (fkRectVertexBoxEmbedding R
              (fkRectRightColumn R, targetRow))) := by
  by_cases hsource : FKRectPrimalFullExploredVertex R S psi
      (fkRectLeftColumn R, i)
  · have hempty :
        FKRectPrimalAdaptivePairedConnectionEvent R S i targetRow psi = ∅ := by
      ext rho
      constructor
      · rintro ⟨hnot, _⟩
        exact (hnot hsource).elim
      · simp
    rw [hempty]
    simp only [Set.indicator_empty, zero_mul, Finset.sum_const_zero]
    exact measureReal_nonneg
  · by_cases htarget : FKRectPrimalFullExploredVertex R S psi
        (fkRectRightColumn R, targetRow)
    · have hempty :
          FKRectPrimalAdaptivePairedConnectionEvent R S i targetRow psi = ∅ := by
        ext rho
        constructor
        · rintro ⟨_, hnot, _⟩
          exact (hnot htarget).elim
        · simp
      rw [hempty]
      simp only [Set.indicator_empty, zero_mul, Finset.sum_const_zero]
      exact measureReal_nonneg
    · let eta := fkRectCutConfigOfFull R psi
      let source : FKRectPrimalUnexploredVertex R S eta.1 :=
        ⟨(fkRectLeftColumn R, i), fun h => hsource
          ((fkRectPrimalFullExploredVertex_iff R S psi _).2 h)⟩
      let target : FKRectPrimalUnexploredVertex R S eta.1 :=
        ⟨(fkRectRightColumn R, targetRow), fun h => htarget
          ((fkRectPrimalFullExploredVertex_iff R S psi _).2 h)⟩
      let A := FKRectPrimalUnexploredConnectionEvent R S eta.1 source target
      have hevent :
          FKRectPrimalAdaptivePairedConnectionEvent R S i targetRow psi =
            FK.ocd_innerRestrict
              (Subtype.val : FKRectPrimalUnexploredVertex R S eta.1 ->
                R.Vertex) ⁻¹' A := by
        ext rho
        constructor
        · rintro ⟨hsource', htarget', hconn⟩
          simpa only [eta, source, target, A] using hconn
        · intro hconn
          exact ⟨hsource, htarget, by
            simpa only [eta, source, target, A] using hconn⟩
      rw [hevent]
      rw [fkRectPrimalAdaptive_condMass_eq_freeUnexplored
        R S psi hp hp1 (zero_lt_one.trans_le hq) A]
      simpa only [A, source, target,
        fkRectPrimalUnexploredBoxEmbedding]
        using fkRectPrimalUnexploredConnection_freeMass_le_boxConn
          R S eta.1 source target hp hp1 hq



def FKRectPrimalFullDistinctPairedWitness
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    (S : Finset (Fin R.height)) (rho : ConfigSpace (Sym2 R.Vertex)) : Prop :=
  (∀ i ∈ S,
    (FK.openSub (fkRectCutGraph R) rho).Reachable
      (fkRectLeftColumn R, i) (fkRectRightColumn R, pair i)) ∧
  (∀ i ∈ S, ∀ j ∈ S, i ≠ j ->
    ¬ (FK.openSub (fkRectCutGraph R) rho).Reachable
      (fkRectLeftColumn R, i) (fkRectLeftColumn R, j))

theorem FKRectPrimalFullDistinctPairedWitness.toDistinctCrossing
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    (S : Finset (Fin R.height)) (rho : ConfigSpace (Sym2 R.Vertex))
    (h : FKRectPrimalFullDistinctPairedWitness R pair S rho) :
    FKRectPrimalFullDistinctCrossingWitness R S rho := by
  exact ⟨fun i hi => ⟨pair i, h.1 i hi⟩, h.2⟩


theorem fkRectPrimalFullDistinctPairedWitness_projection_iff
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    (S : Finset (Fin R.height)) (rho : ConfigSpace (Sym2 R.Vertex)) :
    FKRectPrimalFullDistinctPairedWitness R pair S
        (fkRectPrimalAdaptiveProjection R S rho) <->
      FKRectPrimalFullDistinctPairedWitness R pair S rho := by
  constructor
  · rintro ⟨hpair, hdistinct⟩
    exact ⟨fun i hi =>
        (fkRectPrimalSourceReachable_projection_iff
          R S rho hi _).1 (hpair i hi),
      fun i hi j hj hij hreach => hdistinct i hi j hj hij
        ((fkRectPrimalSourceReachable_projection_iff
          R S rho hi _).2 hreach)⟩
  · rintro ⟨hpair, hdistinct⟩
    exact ⟨fun i hi =>
        (fkRectPrimalSourceReachable_projection_iff
          R S rho hi _).2 (hpair i hi),
      fun i hi j hj hij hreach => hdistinct i hi j hj hij
        ((fkRectPrimalSourceReachable_projection_iff
          R S rho hi _).1 hreach)⟩

theorem fkRectPrimalFullDistinctPairedWitness_fibre_iff
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    (S : Finset (Fin R.height))
    {rho sigma : ConfigSpace (Sym2 R.Vertex)}
    (hproj : fkRectPrimalAdaptiveProjection R S rho =
      fkRectPrimalAdaptiveProjection R S sigma) :
    FKRectPrimalFullDistinctPairedWitness R pair S rho <->
      FKRectPrimalFullDistinctPairedWitness R pair S sigma := by
  rw [← fkRectPrimalFullDistinctPairedWitness_projection_iff
      R pair S rho,
    ← fkRectPrimalFullDistinctPairedWitness_projection_iff
      R pair S sigma,
    hproj]



theorem fkRectPrimalFullDistinctPairedWitness_insert_imp_base
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    (S : Finset (Fin R.height)) (i : Fin R.height)
    (rho : ConfigSpace (Sym2 R.Vertex))
    (h : FKRectPrimalFullDistinctPairedWitness R pair (insert i S) rho) :
    FKRectPrimalFullDistinctPairedWitness R pair S rho := by
  exact ⟨fun j hj => h.1 j (Finset.mem_insert_of_mem hj),
    fun j hj k hk hjk => h.2 j (Finset.mem_insert_of_mem hj)
      k (Finset.mem_insert_of_mem hk) hjk⟩



theorem fkRectPrimalFullDistinctPairedWitness_insert_imp_adaptiveConnection
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    (S : Finset (Fin R.height)) (i : Fin R.height) (hi : i ∉ S)
    (rho : ConfigSpace (Sym2 R.Vertex))
    (h : FKRectPrimalFullDistinctPairedWitness R pair (insert i S) rho) :
    rho ∈ FKRectPrimalAdaptivePairedConnectionEvent R S i (pair i)
      (fkRectPrimalAdaptiveProjection R S rho) := by
  let psi := fkRectPrimalAdaptiveProjection R S rho
  have hdistinct := h.toDistinctCrossing R pair (insert i S) rho
  have hreach := h.1 i (Finset.mem_insert_self i S)
  have hsourceRho : ¬ FKRectPrimalFullExploredVertex R S rho
      (fkRectLeftColumn R, i) :=
    fkRectPrimalFullDistinctCrossingWitness_insert_not_explored_of_reachable
      R S i hi rho hdistinct (SimpleGraph.Reachable.refl _)
  have htargetRho : ¬ FKRectPrimalFullExploredVertex R S rho
      (fkRectRightColumn R, pair i) :=
    fkRectPrimalFullDistinctCrossingWitness_insert_not_explored_of_reachable
      R S i hi rho hdistinct hreach
  have hsourcePsi : ¬ FKRectPrimalFullExploredVertex R S psi
      (fkRectLeftColumn R, i) := by
    intro hexplored
    exact hsourceRho
      ((fkRectPrimalFullExploredVertex_projection_iff R S rho _).1 hexplored)
  have htargetPsi : ¬ FKRectPrimalFullExploredVertex R S psi
      (fkRectRightColumn R, pair i) := by
    intro hexplored
    exact htargetRho
      ((fkRectPrimalFullExploredVertex_projection_iff R S rho _).1 hexplored)
  let eta := fkRectCutConfigOfFull R psi
  let source : FKRectPrimalUnexploredVertex R S eta.1 :=
    ⟨(fkRectLeftColumn R, i), fun hidx => hsourcePsi
      ((fkRectPrimalFullExploredVertex_iff R S psi _).2 hidx)⟩
  let target : FKRectPrimalUnexploredVertex R S eta.1 :=
    ⟨(fkRectRightColumn R, pair i), fun hidx => htargetPsi
      ((fkRectPrimalFullExploredVertex_iff R S psi _).2 hidx)⟩
  have hnotPsi : forall {v : R.Vertex},
      (FK.openSub (fkRectCutGraph R) rho).Reachable
          (fkRectLeftColumn R, i) v ->
        ¬ FKRectPrimalFullExploredVertex R S psi v := by
    intro v hiv hexplored
    have hexploredRho : FKRectPrimalFullExploredVertex R S rho v :=
      (fkRectPrimalFullExploredVertex_projection_iff R S rho v).1 hexplored
    exact fkRectPrimalFullDistinctCrossingWitness_insert_not_explored_of_reachable
      R S i hi rho hdistinct hiv hexploredRho
  have hinduced :
      (FK.openSub (fkRectPrimalUnexploredInducedGraph R S eta.1)
        (FK.ocd_innerRestrict
          (Subtype.val : FKRectPrimalUnexploredVertex R S eta.1 -> R.Vertex)
          rho)).Reachable source target := by
    let G := FK.openSub (fkRectCutGraph R) rho
    let H := FK.openSub (fkRectPrimalUnexploredInducedGraph R S eta.1)
      (FK.ocd_innerRestrict
        (Subtype.val : FKRectPrimalUnexploredVertex R S eta.1 -> R.Vertex)
        rho)
    let liftWalk : forall {x y : R.Vertex} (path : G.Walk x y)
        (hsx : G.Reachable (fkRectLeftColumn R, i) x),
        H.Walk
          ⟨x, fun hidx => hnotPsi hsx
            ((fkRectPrimalFullExploredVertex_iff R S psi _).2 hidx)⟩
          ⟨y, fun hidx => hnotPsi (hsx.trans path.reachable)
            ((fkRectPrimalFullExploredVertex_iff R S psi _).2 hidx)⟩ := by
      intro x y path
      induction path with
      | nil => intro _; exact SimpleGraph.Walk.nil
      | @cons x y z hxy path ih =>
          intro hsx
          have hstep : H.Adj
              ⟨x, fun hidx => hnotPsi hsx
                ((fkRectPrimalFullExploredVertex_iff R S psi _).2 hidx)⟩
              ⟨y, fun hidx => hnotPsi (hsx.trans hxy.reachable)
                ((fkRectPrimalFullExploredVertex_iff R S psi _).2 hidx)⟩ := by
            exact ⟨hxy.1, by
              simpa [FK.ocd_innerRestrict, FK.ocd_innerEdge_mk] using hxy.2⟩
          exact SimpleGraph.Walk.cons hstep
            (ih (hsx.trans hxy.reachable))
    exact hreach.elim fun path =>
      ⟨by simpa only [source, target, G, H] using
        liftWalk path (SimpleGraph.Reachable.refl (fkRectLeftColumn R, i))⟩
  exact ⟨hsourcePsi, htargetPsi, hinduced⟩



theorem fkRectPrimalFullDistinctPairedWitness_step
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    (S : Finset (Fin R.height)) (i : Fin R.height) (hi : i ∉ S)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectCutGraph R) p q)
        {rho | FKRectPrimalFullDistinctPairedWitness
          R pair (insert i S) rho} <=
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (FK.boxConnEvent 2 (R.width + R.height)
            (fkRectVertexBoxEmbedding R (fkRectLeftColumn R, i))
            (fkRectVertexBoxEmbedding R (fkRectRightColumn R, pair i))) *
        StatMech.Probability.finiteEventMass
          (FK.fkProb (fkRectCutGraph R) p q)
          {rho | FKRectPrimalFullDistinctPairedWitness R pair S rho} := by
  classical
  let P := fkRectPrimalAdaptiveProjection R S
  let Base : Set (ConfigSpace (Sym2 R.Vertex)) :=
    {rho | FKRectPrimalFullDistinctPairedWitness R pair S rho}
  let Inserted : Set (ConfigSpace (Sym2 R.Vertex)) :=
    {rho | FKRectPrimalFullDistinctPairedWitness R pair (insert i S) rho}
  let Arm : ConfigSpace (Sym2 R.Vertex) ->
      Set (ConfigSpace (Sym2 R.Vertex)) := fun psi =>
    FKRectPrimalAdaptivePairedConnectionEvent R S i (pair i) psi
  let a := (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 (Site 2)))).real
      (FK.boxConnEvent 2 (R.width + R.height)
        (fkRectVertexBoxEmbedding R (fkRectLeftColumn R, i))
        (fkRectVertexBoxEmbedding R (fkRectRightColumn R, pair i)))
  apply StatMech.Probability.finiteEventMass_adaptive_fibre_step
    (FK.fkProb (fkRectCutGraph R) p q)
    (fun rho => FK.fkProb_nonneg (fkRectCutGraph R)
      hp hp1 (zero_lt_one.trans_le hq) rho)
    P (fun rho => fkRectPrimalAdaptiveProjection_idem R S rho)
    Base Inserted Arm
  · intro rho sigma hproj
    exact fkRectPrimalFullDistinctPairedWitness_fibre_iff
      R pair S hproj
  · intro rho hrho
    exact ⟨fkRectPrimalFullDistinctPairedWitness_insert_imp_base
        R pair S i rho hrho,
      fkRectPrimalFullDistinctPairedWitness_insert_imp_adaptiveConnection
        R pair S i hi rho hrho⟩
  · intro psi hpsiImage
    obtain ⟨rho, _, hrho⟩ := Finset.mem_image.mp hpsiImage
    have hfixed : P psi = psi := by
      rw [← hrho]
      exact fkRectPrimalAdaptiveProjection_idem R S rho
    let F := fkRectPrimalAdaptiveInsideEdges R S psi
    let M := ∑ sigma ∈ FK.condFibre F psi,
      FK.fkProb (fkRectCutGraph R) p q sigma
    let C := ∑ rho,
      (Arm psi).indicator (fun _ => (1 : Real)) rho *
        FK.condBcProb (fkRectCutGraph R) (⊥ : SimpleGraph R.Vertex)
          p q F psi rho
    have hfilter : Finset.univ.filter (fun rho => P rho = psi) =
        FK.condFibre F psi :=
      fkRectPrimalAdaptiveProjection_filter_eq_condFibre R S psi hfixed
    have hraw := FK.bcProb_event_fibre_eq_mass_mul_cond
      (fkRectCutGraph R) (⊥ : SimpleGraph R.Vertex)
      hp hp1 (zero_lt_one.trans_le hq) F psi (Arm psi)
    simp_rw [FK.bcProb_bot_eq_fkProb] at hraw
    have hboundary : boundaryCliqueGraph (fun _ : R.Vertex => False) =
        (⊥ : SimpleGraph R.Vertex) := by
      apply SimpleGraph.ext
      ext x y
      rw [boundaryCliqueGraph_adj]
      simp [SimpleGraph.bot_adj]
    have hcond : C <= a := by
      simpa [C, a, hboundary, Arm] using
        fkRectPrimalAdaptivePairedConnectionEvent_condMass_le_boxConn
          R S i (pair i) psi hp hp1 hq
    have hM : 0 <= M := Finset.sum_nonneg fun sigma _ =>
      FK.fkProb_nonneg (fkRectCutGraph R)
        hp hp1 (zero_lt_one.trans_le hq) sigma
    have hind : forall omega : ConfigSpace (Sym2 R.Vertex),
        (Arm psi).indicator (FK.fkProb (fkRectCutGraph R) p q) omega =
          FK.fkProb (fkRectCutGraph R) p q omega *
            (Arm psi).indicator (fun _ => (1 : Real)) omega := by
      intro omega
      by_cases hArm : omega ∈ Arm psi <;> simp [hArm]
    calc
      (∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          (Arm psi).indicator
            (FK.fkProb (fkRectCutGraph R) p q) omega) = M * C := by
        rw [hfilter]
        simp_rw [hind]
        simpa [M, C, mul_comm] using hraw
      _ <= M * a := mul_le_mul_of_nonneg_left hcond hM
      _ = a * M := by ring
      _ = a * ∑ omega ∈
          (Finset.univ.filter fun omega => P omega = psi),
            FK.fkProb (fkRectCutGraph R) p q omega := by rw [hfilter]



def fkRectPrimalPairedConnectionFactor
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (i : Fin R.height) : Real :=
  (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 (Site 2)))).real
      (FK.boxConnEvent 2 (R.width + R.height)
        (fkRectVertexBoxEmbedding R (fkRectLeftColumn R, i))
        (fkRectVertexBoxEmbedding R (fkRectRightColumn R, pair i)))

theorem fkRectPrimalPairedConnectionFactor_nonneg
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (i : Fin R.height) :
    0 <= fkRectPrimalPairedConnectionFactor R pair hp hp1 hq i :=
  measureReal_nonneg

theorem fkRectPrimalPairedConnectionFactor_le_one
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (i : Fin R.height) :
    fkRectPrimalPairedConnectionFactor R pair hp hp1 hq i <= 1 :=
  measureReal_le_one



theorem fkRectPrimalFullDistinctPairedWitness_mass_le_prod
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (S : Finset (Fin R.height)) :
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectCutGraph R) p q)
        {rho | FKRectPrimalFullDistinctPairedWitness R pair S rho} <=
      ∏ i ∈ S, fkRectPrimalPairedConnectionFactor R pair hp hp1 hq i := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      calc
        StatMech.Probability.finiteEventMass
            (FK.fkProb (fkRectCutGraph R) p q)
            {rho | FKRectPrimalFullDistinctPairedWitness R pair ∅ rho} = 1 := by
          unfold StatMech.Probability.finiteEventMass
          have hevent : {rho : ConfigSpace (Sym2 R.Vertex) |
              FKRectPrimalFullDistinctPairedWitness R pair ∅ rho} =
              Set.univ := by
            ext rho
            simp [FKRectPrimalFullDistinctPairedWitness]
          rw [hevent]
          simpa using FK.fkProb_sum_eq_one (fkRectCutGraph R)
            hp hp1 (zero_lt_one.trans_le hq)
        _ <= ∏ i ∈ (∅ : Finset (Fin R.height)),
            fkRectPrimalPairedConnectionFactor R pair hp hp1 hq i := by simp
  | @insert i S hi ih =>
      calc
        StatMech.Probability.finiteEventMass
            (FK.fkProb (fkRectCutGraph R) p q)
            {rho | FKRectPrimalFullDistinctPairedWitness
              R pair (insert i S) rho} <=
          fkRectPrimalPairedConnectionFactor R pair hp hp1 hq i *
            StatMech.Probability.finiteEventMass
              (FK.fkProb (fkRectCutGraph R) p q)
              {rho | FKRectPrimalFullDistinctPairedWitness R pair S rho} := by
                simpa only [fkRectPrimalPairedConnectionFactor] using
                  fkRectPrimalFullDistinctPairedWitness_step
                    R pair S i hi hp hp1 hq
        _ <= fkRectPrimalPairedConnectionFactor R pair hp hp1 hq i *
            (∏ j ∈ S,
              fkRectPrimalPairedConnectionFactor R pair hp hp1 hq j) :=
          mul_le_mul_of_nonneg_left ih
            (fkRectPrimalPairedConnectionFactor_nonneg
              R pair hp hp1 hq i)
        _ = ∏ j ∈ insert i S,
            fkRectPrimalPairedConnectionFactor R pair hp hp1 hq j := by
          simp [hi]





theorem fkRectPrimalFullDistinctPairedWitness_mass_le_prod_erase
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (S : Finset (Fin R.height)) (first : Fin R.height) (hfirst : first ∈ S) :
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectCutGraph R) p q)
        {rho | FKRectPrimalFullDistinctPairedWitness R pair S rho} <=
      ∏ i ∈ S.erase first,
        fkRectPrimalPairedConnectionFactor R pair hp hp1 hq i := by
  let f := fkRectPrimalPairedConnectionFactor R pair hp hp1 hq
  have hfull := fkRectPrimalFullDistinctPairedWitness_mass_le_prod
    R pair hp hp1 hq S
  have hnonneg : 0 <= ∏ i ∈ S.erase first, f i :=
    Finset.prod_nonneg fun i _ =>
      fkRectPrimalPairedConnectionFactor_nonneg R pair hp hp1 hq i
  have hfactor : f first <= 1 :=
    fkRectPrimalPairedConnectionFactor_le_one R pair hp hp1 hq first
  calc
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectCutGraph R) p q)
        {rho | FKRectPrimalFullDistinctPairedWitness R pair S rho} <=
      ∏ i ∈ S, f i := hfull
    _ = f first * ∏ i ∈ S.erase first, f i := by
      exact (Finset.mul_prod_erase S f hfirst).symm
    _ <= 1 * ∏ i ∈ S.erase first, f i :=
      mul_le_mul_of_nonneg_right hfactor hnonneg
    _ = ∏ i ∈ S.erase first, f i := one_mul _


def FKRectPrimalStablePairedWitnessCore
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    (S : Finset (Fin R.height)) (eta : R.Configuration) : Prop :=
  FKRectPrimalFullDistinctPairedWitness R pair S
    (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))

theorem fkRectPrimalFullDistinctPairedWitness_congr_openSub
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    (S : Finset (Fin R.height))
    {rho sigma : ConfigSpace (Sym2 R.Vertex)}
    (hgraph : FK.openSub (fkRectCutGraph R) rho =
      FK.openSub (fkRectCutGraph R) sigma) :
    FKRectPrimalFullDistinctPairedWitness R pair S rho <->
      FKRectPrimalFullDistinctPairedWitness R pair S sigma := by
  unfold FKRectPrimalFullDistinctPairedWitness
  rw [hgraph]

theorem fkRectPrimalStablePairedWitness_cutConfigOfFull_iff
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    (S : Finset (Fin R.height)) (rho : ConfigSpace (Sym2 R.Vertex)) :
    FKRectPrimalStablePairedWitnessCore R pair S
        (fkRectCutConfigOfFull R rho).1 <->
      FKRectPrimalFullDistinctPairedWitness R pair S rho := by
  unfold FKRectPrimalStablePairedWitnessCore
  have hforce : fkRectForceCutClosed R (fkRectCutConfigOfFull R rho).1 =
      (fkRectCutConfigOfFull R rho).1 := (fkRectCutConfigOfFull R rho).2
  rw [hforce]
  apply fkRectPrimalFullDistinctPairedWitness_congr_openSub
  calc
    FK.openSub (fkRectCutGraph R)
        (fkRectFullGraphConfiguration R (fkRectCutConfigOfFull R rho).1) =
      fkRectOpenGraph R (fkRectCutConfigOfFull R rho).1 :=
        fkRectCut_openSub_eq R (fkRectCutConfigOfFull R rho)
    _ = FK.openSub (fkRectCutGraph R) rho :=
      fkRectOpenGraph_cutConfigOfFull R rho

theorem fkRectCutGraph_stablePairedWitnessEvent_eq
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    (S : Finset (Fin R.height)) :
    FK.ecz_closeOff (fkRectCutGraph R) ⁻¹'
        fkRectCutEdgeEvent R
          {eta | FKRectPrimalStablePairedWitnessCore R pair S eta} =
      {rho | FKRectPrimalFullDistinctPairedWitness R pair S rho} := by
  ext rho
  change FKRectPrimalStablePairedWitnessCore R pair S
      ((fkRectCutClosedEdgeConfigEquiv R).symm
        (FK.ecz_closeOff (fkRectCutGraph R) rho)).1 <-> _
  exact fkRectPrimalStablePairedWitness_cutConfigOfFull_iff R pair S rho



theorem fkRectCriticalCutFree_stablePairedWitness_eq_finiteEventMass
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    {q : Real} (hq : 1 <= q) (S : Finset (Fin R.height)) :
    fkRectCriticalCutFreeEventMass R q
        {eta | FKRectPrimalStablePairedWitnessCore R pair S eta} =
      StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectCutGraph R) (fkRectCriticalP q) q)
        {rho | FKRectPrimalFullDistinctPairedWitness R pair S rho} := by
  rw [fkRectCriticalCutFreeEventMass_eq_cutGraph R hq,
    fkRectCutGraph_stablePairedWitnessEvent_eq R pair S]
  unfold StatMech.Probability.finiteEventMass
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hmem : FKRectPrimalFullDistinctPairedWitness R pair S rho
  · simp [Set.indicator, hmem]
  · simp [Set.indicator, hmem]



theorem fkRectCriticalCutFree_stablePairedWitness_le_prod
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    {q : Real} (hq : 1 <= q) (S : Finset (Fin R.height)) :
    fkRectCriticalCutFreeEventMass R q
        {eta | FKRectPrimalStablePairedWitnessCore R pair S eta} <=
      ∏ i ∈ S,
        fkRectPrimalPairedConnectionFactor R pair
          (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
          (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) hq i := by
  rw [fkRectCriticalCutFree_stablePairedWitness_eq_finiteEventMass
    R pair hq S]
  exact fkRectPrimalFullDistinctPairedWitness_mass_le_prod R pair
    (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
    (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) hq S

end

end StatMech.FrontierD

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectHorizontalCylinderAdaptiveProjection
import Code.FrontierD.FKRectHorizontalCylinderPlanarization
import Code.FrontierD.FKRectHorizontalCylinderTailPower
import Code.Probability.AdaptiveFibreStep
import Code.Probability.FiniteWitnessInsertionIteration
import Code.FK.ConditionalFibreMass
import Code.FK.BoxConnectionFullConnection










open MeasureTheory SimpleGraph StatMech.Lattice

namespace StatMech.FrontierD

noncomputable section



def FKRectHorizontalCylinderAdaptivePairedConnectionEvent
    (R : FKRectTorus) (S : Finset (Fin R.width))
    (x targetX : Fin R.width) (psi : ConfigSpace (Sym2 R.Vertex)) :
    Set (ConfigSpace (Sym2 R.Vertex)) :=
  {rho | ∃ source target :
      FKRectHorizontalCylinderUnexploredVertex R psi S,
    source.1 = (x, fkRectBottomRow R) ∧
    target.1 = (targetX, fkRectTopRow R) ∧
    (FK.openSub
      (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) psi
        (fkRectHorizontalCylinderBottomRoots R S))
      (FK.ocd_innerRestrict
        (Subtype.val :
          FKRectHorizontalCylinderUnexploredVertex R psi S → R.Vertex)
        rho)).Reachable source target}



theorem fkRectHorizontalCylinderAdaptivePairedConnectionEvent_condMass_le_boxConn
    (R : FKRectTorus) (S : Finset (Fin R.width))
    (x targetX : Fin R.width) (psi : ConfigSpace (Sym2 R.Vertex))
    (P : FKRectHorizontalCylinderUnexploredPlanarization R psi S)
    (hsource : ¬ FKRectHorizontalCylinderExploredVertex R psi S
      (x, fkRectBottomRow R))
    (htarget : ¬ FKRectHorizontalCylinderExploredVertex R psi S
      (targetX, fkRectTopRow R))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (∑ rho : ConfigSpace (Sym2 R.Vertex),
        (FKRectHorizontalCylinderAdaptivePairedConnectionEvent
          R S x targetX psi).indicator (fun _ => (1 : Real)) rho *
        FK.condBcProb (fkRectHorizontalCylinderGraph R)
          (boundaryCliqueGraph (fun _ : R.Vertex => False)) p q
          (fkRectHorizontalCylinderAdaptiveInsideEdges R S psi) psi rho) ≤
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (FK.boxConnEvent 2 P.radius
            (P.embedding
              ⟨(x, fkRectBottomRow R), hsource⟩)
            (P.embedding
              ⟨(targetX, fkRectTopRow R), htarget⟩)) := by
  let source : FKRectHorizontalCylinderUnexploredVertex R psi S :=
    ⟨(x, fkRectBottomRow R), hsource⟩
  let target : FKRectHorizontalCylinderUnexploredVertex R psi S :=
    ⟨(targetX, fkRectTopRow R), htarget⟩
  let A := FKFiniteConnectionEvent
    (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) psi
      (fkRectHorizontalCylinderBottomRoots R S)) source target
  have hevent :
      FKRectHorizontalCylinderAdaptivePairedConnectionEvent
          R S x targetX psi =
        FK.ocd_innerRestrict
          (Subtype.val :
            FKRectHorizontalCylinderUnexploredVertex R psi S → R.Vertex) ⁻¹'
          A := by
    ext rho
    constructor
    · rintro ⟨source', target', hsourceVal, htargetVal, hconn⟩
      have hs : source' = source := by
        apply Subtype.ext
        exact hsourceVal
      have ht : target' = target := by
        apply Subtype.ext
        exact htargetVal
      simpa [A, hs, ht] using hconn
    · intro hconn
      exact ⟨source, target, rfl, rfl, by simpa [A] using hconn⟩
  rw [hevent]
  simpa [source, target,
    fkRectHorizontalCylinderAdaptiveInsideEdges] using
    fkRectHorizontalCylinder_conditionalConnection_le_boxConn
      R psi S P source target hp hp1 hq



theorem fkRectHorizontalCylinderAdaptivePairedConnectionEvent_condMass_le_twoPoint
    (R : FKRectTorus) (S : Finset (Fin R.width))
    (x targetX : Fin R.width) (psi : ConfigSpace (Sym2 R.Vertex))
    (P : FKRectHorizontalCylinderUnexploredPlanarization R psi S)
    (hsource : ¬ FKRectHorizontalCylinderExploredVertex R psi S
      (x, fkRectBottomRow R))
    (htarget : ¬ FKRectHorizontalCylinderExploredVertex R psi S
      (targetX, fkRectTopRow R))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (∑ rho : ConfigSpace (Sym2 R.Vertex),
        (FKRectHorizontalCylinderAdaptivePairedConnectionEvent
          R S x targetX psi).indicator (fun _ => (1 : Real)) rho *
        FK.condBcProb (fkRectHorizontalCylinderGraph R)
          (boundaryCliqueGraph (fun _ : R.Vertex => False)) p q
          (fkRectHorizontalCylinderAdaptiveInsideEdges R S psi) psi rho) ≤
      FK.infiniteTwoPointReal
        (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 (Site 2))))
        (P.embedding ⟨(x, fkRectBottomRow R), hsource⟩).1
        (P.embedding ⟨(targetX, fkRectTopRow R), htarget⟩).1 := by
  exact (fkRectHorizontalCylinderAdaptivePairedConnectionEvent_condMass_le_boxConn
    R S x targetX psi P hsource htarget hp hp1 hq).trans
      (FK.measureReal_boxConnEvent_le_infiniteTwoPointReal
        2 P.radius
        (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq))
        (P.embedding ⟨(x, fkRectBottomRow R), hsource⟩)
        (P.embedding ⟨(targetX, fkRectTopRow R), htarget⟩))



theorem fkRectHorizontalCylinderDistinctPairedWitness_insert_imp_adaptiveConnection
    (R : FKRectTorus) (pair : Fin R.width → Fin R.width)
    (S : Finset (Fin R.width)) (x : Fin R.width) (hx : x ∉ S)
    (rho : ConfigSpace (Sym2 R.Vertex))
    (h : FKRectHorizontalCylinderDistinctPairedWitness
      R pair (insert x S) rho) :
    rho ∈ FKRectHorizontalCylinderAdaptivePairedConnectionEvent
      R S x (pair x)
        (fkRectHorizontalCylinderAdaptiveProjection R S rho) := by
  let psi := fkRectHorizontalCylinderAdaptiveProjection R S rho
  let bottom : R.Vertex := (x, fkRectBottomRow R)
  let top : R.Vertex := (pair x, fkRectTopRow R)
  have hbt := h.1 x (Finset.mem_insert_self x S)
  have hnotPsi : ∀ {v : R.Vertex},
      (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Reachable bottom v →
        ¬ FKRectHorizontalCylinderExploredVertex R psi S v := by
    intro v hxv hv
    have hvRho : FKRectHorizontalCylinderExploredVertex R rho S v :=
      (fkRectHorizontalCylinderExploredVertex_projection_iff
        R S rho v).1 hv
    exact not_horizontalCylinderExplored_of_fresh_reachable
      R rho pair (insert x S) S h
      (fun _ hy => Finset.mem_insert_of_mem hy)
      (Finset.mem_insert_self x S) hx hxv hvRho
  let source : FKRectHorizontalCylinderUnexploredVertex R psi S :=
    ⟨bottom, hnotPsi (SimpleGraph.Reachable.refl bottom)⟩
  let target : FKRectHorizontalCylinderUnexploredVertex R psi S :=
    ⟨top, hnotPsi hbt⟩
  have hinduced :
      (FK.openSub
        (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) psi
          (fkRectHorizontalCylinderBottomRoots R S))
        (FK.ocd_innerRestrict
          (Subtype.val :
            FKRectHorizontalCylinderUnexploredVertex R psi S → R.Vertex)
          rho)).Reachable source target := by
    let G := FK.openSub (fkRectHorizontalCylinderGraph R) rho
    let H := FK.openSub
      (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) psi
        (fkRectHorizontalCylinderBottomRoots R S))
      (FK.ocd_innerRestrict
        (Subtype.val :
          FKRectHorizontalCylinderUnexploredVertex R psi S → R.Vertex) rho)
    let liftWalk : ∀ {u v : R.Vertex} (path : G.Walk u v)
        (hbu : G.Reachable bottom u),
        H.Walk
          ⟨u, hnotPsi hbu⟩
          ⟨v, hnotPsi (hbu.trans path.reachable)⟩ := by
      intro u v path
      induction path with
      | nil => intro _; exact SimpleGraph.Walk.nil
      | @cons u v w huv path ih =>
          intro hbu
          have hstep : H.Adj
              ⟨u, hnotPsi hbu⟩
              ⟨v, hnotPsi (hbu.trans huv.reachable)⟩ := by
            exact ⟨huv.1, by
              simpa [FK.ocd_innerRestrict, FK.ocd_innerEdge_mk] using huv.2⟩
          exact SimpleGraph.Walk.cons hstep
            (ih (hbu.trans huv.reachable))
    exact hbt.elim fun path =>
      ⟨by simpa only [source, target, G, H] using
        liftWalk path (SimpleGraph.Reachable.refl bottom)⟩
  exact ⟨source, target, rfl, rfl, hinduced⟩



theorem fkRectHorizontalCylinderDistinctPairedWitness_step_of_planarization
    (R : FKRectTorus) (pair : Fin R.width → Fin R.width)
    (S : Finset (Fin R.width)) (x : Fin R.width) (hx : x ∉ S)
    (planarize : ∀ psi : ConfigSpace (Sym2 R.Vertex),
      FKRectHorizontalCylinderDistinctPairedWitness R pair S psi →
        FKRectHorizontalCylinderUnexploredPlanarization R psi S)
    {p q a : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ha : 0 ≤ a)
    (htwo : ∀ (psi : ConfigSpace (Sym2 R.Vertex))
        (hbase : FKRectHorizontalCylinderDistinctPairedWitness R pair S psi)
        (hsource : ¬ FKRectHorizontalCylinderExploredVertex R psi S
          (x, fkRectBottomRow R))
        (htarget : ¬ FKRectHorizontalCylinderExploredVertex R psi S
          (pair x, fkRectTopRow R)),
      FK.infiniteTwoPointReal
        (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 (Site 2))))
        ((planarize psi hbase).embedding
          ⟨(x, fkRectBottomRow R), hsource⟩).1
        ((planarize psi hbase).embedding
          ⟨(pair x, fkRectTopRow R), htarget⟩).1 ≤ a) :
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectHorizontalCylinderGraph R) p q)
        {rho | FKRectHorizontalCylinderDistinctPairedWitness
          R pair (insert x S) rho} ≤
      a * StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectHorizontalCylinderGraph R) p q)
        {rho | FKRectHorizontalCylinderDistinctPairedWitness
          R pair S rho} := by
  classical
  let Proj := fkRectHorizontalCylinderAdaptiveProjection R S
  let Base : Set (ConfigSpace (Sym2 R.Vertex)) :=
    {rho | FKRectHorizontalCylinderDistinctPairedWitness R pair S rho}
  let Inserted : Set (ConfigSpace (Sym2 R.Vertex)) :=
    {rho | FKRectHorizontalCylinderDistinctPairedWitness
      R pair (insert x S) rho}
  let Arm : ConfigSpace (Sym2 R.Vertex) →
      Set (ConfigSpace (Sym2 R.Vertex)) := fun psi =>
    FKRectHorizontalCylinderAdaptivePairedConnectionEvent
      R S x (pair x) psi
  apply StatMech.Probability.finiteEventMass_adaptive_fibre_step_on_base
    (FK.fkProb (fkRectHorizontalCylinderGraph R) p q)
    (fun rho => FK.fkProb_nonneg (fkRectHorizontalCylinderGraph R)
      hp hp1 (zero_lt_one.trans_le hq) rho)
    Proj
    (fun rho => fkRectHorizontalCylinderAdaptiveProjection_idem R S rho)
    Base Inserted Arm
  · intro rho sigma hproj
    exact fkRectHorizontalCylinderDistinctPairedWitness_fibre_iff
      R pair S hproj
  · intro rho hrho
    exact ⟨fkRectHorizontalCylinderDistinctPairedWitness_insert_imp_base
        R pair S x rho hrho,
      fkRectHorizontalCylinderDistinctPairedWitness_insert_imp_adaptiveConnection
        R pair S x hx rho hrho⟩
  · intro psi hpsiImage hbasePsi
    have hbase : FKRectHorizontalCylinderDistinctPairedWitness
        R pair S psi := by
      simpa [Base] using hbasePsi
    let Plan := planarize psi hbase
    obtain ⟨rho, _, hrho⟩ := Finset.mem_image.mp hpsiImage
    have hfixed : Proj psi = psi := by
      rw [← hrho]
      exact fkRectHorizontalCylinderAdaptiveProjection_idem R S rho
    let F := fkRectHorizontalCylinderAdaptiveInsideEdges R S psi
    let M := ∑ sigma ∈ FK.condFibre F psi,
      FK.fkProb (fkRectHorizontalCylinderGraph R) p q sigma
    let C := ∑ sigma,
      (Arm psi).indicator (fun _ => (1 : Real)) sigma *
        FK.condBcProb (fkRectHorizontalCylinderGraph R)
          (⊥ : SimpleGraph R.Vertex) p q F psi sigma
    have hfilter : Finset.univ.filter (fun rho => Proj rho = psi) =
        FK.condFibre F psi :=
      fkRectHorizontalCylinderAdaptiveProjection_filter_eq_condFibre
        R S psi hfixed
    have hraw := FK.condBcProb_event_fibre_eq_mass_mul_cond
      (fkRectHorizontalCylinderGraph R) (⊥ : SimpleGraph R.Vertex)
      hp hp1 (zero_lt_one.trans_le hq) F psi (Arm psi)
    simp_rw [FK.bcProb_bot_eq_fkProb] at hraw
    have hboundary : boundaryCliqueGraph (fun _ : R.Vertex => False) =
        (⊥ : SimpleGraph R.Vertex) := by
      apply SimpleGraph.ext
      ext u v
      rw [boundaryCliqueGraph_adj]
      simp [SimpleGraph.bot_adj]
    have hcond : C ≤ a := by
      by_cases hsource : FKRectHorizontalCylinderExploredVertex R psi S
          (x, fkRectBottomRow R)
      · have hempty : Arm psi = ∅ := by
          ext sigma
          constructor
          · rintro ⟨source, _, hsourceVal, _⟩
            exact (source.2 (hsourceVal ▸ hsource)).elim
          · simp
        simpa [C, hempty] using ha
      · by_cases htarget : FKRectHorizontalCylinderExploredVertex R psi S
            (pair x, fkRectTopRow R)
        · have hempty : Arm psi = ∅ := by
            ext sigma
            constructor
            · rintro ⟨_, target, _, htargetVal, _⟩
              exact (target.2 (htargetVal ▸ htarget)).elim
            · simp
          simpa [C, hempty] using ha
        · have hpair :=
            fkRectHorizontalCylinderAdaptivePairedConnectionEvent_condMass_le_twoPoint
              R S x (pair x) psi Plan
              hsource htarget hp hp1 hq
          have hcap := htwo psi hbase hsource htarget
          have hpair' : C ≤
              FK.infiniteTwoPointReal
                (FK.freeInfiniteVolume 2 hp hp1
                  (zero_lt_one.trans_le hq) :
                  Measure (ConfigSpace (Sym2 (Site 2))))
                (Plan.embedding
                  ⟨(x, fkRectBottomRow R), hsource⟩).1
                (Plan.embedding
                  ⟨(pair x, fkRectTopRow R), htarget⟩).1 := by
            simpa [C, Arm, F, hboundary] using hpair
          exact hpair'.trans hcap
    have hM : 0 ≤ M := Finset.sum_nonneg fun sigma _ =>
      FK.fkProb_nonneg (fkRectHorizontalCylinderGraph R)
        hp hp1 (zero_lt_one.trans_le hq) sigma
    have hind : ∀ omega : ConfigSpace (Sym2 R.Vertex),
        (Arm psi).indicator
            (FK.fkProb (fkRectHorizontalCylinderGraph R) p q) omega =
          FK.fkProb (fkRectHorizontalCylinderGraph R) p q omega *
            (Arm psi).indicator (fun _ => (1 : Real)) omega := by
      intro omega
      by_cases hArm : omega ∈ Arm psi <;> simp [hArm]
    calc
      (∑ omega ∈ (Finset.univ.filter fun omega => Proj omega = psi),
          (Arm psi).indicator
            (FK.fkProb (fkRectHorizontalCylinderGraph R) p q) omega) =
        M * C := by
          rw [hfilter]
          simp_rw [hind]
          simpa [M, C, mul_comm] using hraw
      _ ≤ M * a := mul_le_mul_of_nonneg_left hcond hM
      _ = a * M := by ring
      _ = a * ∑ omega ∈
          (Finset.univ.filter fun omega => Proj omega = psi),
            FK.fkProb (fkRectHorizontalCylinderGraph R) p q omega := by
        rw [hfilter]



theorem fkRectHorizontalCylinderDistinctPairedWitness_mass_le_pow_erase_of_step
    (R : FKRectTorus) (pair : Fin R.width → Fin R.width)
    {p q a : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ha : 0 ≤ a)
    (step : ∀ (T : Finset (Fin R.width)) (first : Fin R.width),
      first ∈ T → ∀ (x : Fin R.width), x ∉ T →
      StatMech.Probability.finiteEventMass
          (FK.fkProb (fkRectHorizontalCylinderGraph R) p q)
          {rho | FKRectHorizontalCylinderDistinctPairedWitness
            R pair (insert x T) rho} ≤
        a * StatMech.Probability.finiteEventMass
          (FK.fkProb (fkRectHorizontalCylinderGraph R) p q)
          {rho | FKRectHorizontalCylinderDistinctPairedWitness
            R pair T rho})
    (S : Finset (Fin R.width)) (first : Fin R.width) (hfirst : first ∈ S) :
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectHorizontalCylinderGraph R) p q)
        {rho | FKRectHorizontalCylinderDistinctPairedWitness R pair S rho} ≤
      a ^ (S.erase first).card := by
  exact StatMech.Probability.finiteEventMass_le_pow_erase_of_insert_step
    (FK.fkProb (fkRectHorizontalCylinderGraph R) p q)
    (fun rho => FK.fkProb_nonneg (fkRectHorizontalCylinderGraph R)
      hp hp1 (zero_lt_one.trans_le hq) rho)
    (FK.fkProb_sum_eq_one (fkRectHorizontalCylinderGraph R)
      hp hp1 (zero_lt_one.trans_le hq))
    (fun T rho =>
      FKRectHorizontalCylinderDistinctPairedWitness R pair T rho)
    ha step S first hfirst



theorem fkRectHorizontalCylinderDistinctPairedWitness_mass_le_pow_erase_of_planarization
    (R : FKRectTorus) (pair : Fin R.width → Fin R.width)
    {p q a : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ha : 0 ≤ a)
    (planarize : ∀ (T : Finset (Fin R.width)), T.Nonempty →
      ∀ (psi : ConfigSpace (Sym2 R.Vertex)),
        FKRectHorizontalCylinderDistinctPairedWitness R pair T psi →
          FKRectHorizontalCylinderUnexploredPlanarization R psi T)
    (htwo : ∀ (T : Finset (Fin R.width)) (hT : T.Nonempty)
        (x : Fin R.width) (hx : x ∉ T)
        (psi : ConfigSpace (Sym2 R.Vertex))
        (hbase : FKRectHorizontalCylinderDistinctPairedWitness R pair T psi)
        (hsource : ¬ FKRectHorizontalCylinderExploredVertex R psi T
          (x, fkRectBottomRow R))
        (htarget : ¬ FKRectHorizontalCylinderExploredVertex R psi T
          (pair x, fkRectTopRow R)),
      FK.infiniteTwoPointReal
        (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 (Site 2))))
        ((planarize T hT psi hbase).embedding
          ⟨(x, fkRectBottomRow R), hsource⟩).1
        ((planarize T hT psi hbase).embedding
          ⟨(pair x, fkRectTopRow R), htarget⟩).1 ≤ a)
    (S : Finset (Fin R.width)) (first : Fin R.width) (hfirst : first ∈ S) :
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectHorizontalCylinderGraph R) p q)
        {rho | FKRectHorizontalCylinderDistinctPairedWitness R pair S rho} ≤
      a ^ (S.erase first).card := by
  apply fkRectHorizontalCylinderDistinctPairedWitness_mass_le_pow_erase_of_step
    R pair hp hp1 hq ha
  · intro T anchor hanchor x hx
    let hT : T.Nonempty := ⟨anchor, hanchor⟩
    exact fkRectHorizontalCylinderDistinctPairedWitness_step_of_planarization
      R pair T x hx (planarize T hT) hp hp1 hq ha
        (htwo T hT x hx)
  · exact hfirst



theorem fkRectHorizontalCylinderCrossingTail_le_pow_pred_of_planarization
    (R : FKRectTorus) {p q a : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) (ha : 0 ≤ a)
    (planarize : ∀ (pair : Fin R.width → Fin R.width)
      (T : Finset (Fin R.width)), T.Nonempty →
      ∀ (psi : ConfigSpace (Sym2 R.Vertex)),
        FKRectHorizontalCylinderDistinctPairedWitness R pair T psi →
          FKRectHorizontalCylinderUnexploredPlanarization R psi T)
    (htwo : ∀ (pair : Fin R.width → Fin R.width)
        (T : Finset (Fin R.width)) (hT : T.Nonempty)
        (x : Fin R.width) (hx : x ∉ T)
        (psi : ConfigSpace (Sym2 R.Vertex))
        (hbase : FKRectHorizontalCylinderDistinctPairedWitness R pair T psi)
        (hsource : ¬ FKRectHorizontalCylinderExploredVertex R psi T
          (x, fkRectBottomRow R))
        (htarget : ¬ FKRectHorizontalCylinderExploredVertex R psi T
          (pair x, fkRectTopRow R)),
      FK.infiniteTwoPointReal
        (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 (Site 2))))
        ((planarize pair T hT psi hbase).embedding
          ⟨(x, fkRectBottomRow R), hsource⟩).1
        ((planarize pair T hT psi hbase).embedding
          ⟨(pair x, fkRectTopRow R), htarget⟩).1 ≤ a)
    (n : Nat) (hn : 0 < n) :
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectHorizontalCylinderGraph R) p q)
        {rho | n ≤ fkRectHorizontalCylinderCrossingClusterCount R rho} ≤
      Nat.choose R.width n * R.width ^ R.width * a ^ (n - 1) := by
  apply fkRectHorizontalCylinderCrossingTail_le_choose_mul_pairCount_mul_pow_pred
    R (FK.fkProb (fkRectHorizontalCylinderGraph R) p q)
    (fun rho => FK.fkProb_nonneg (fkRectHorizontalCylinderGraph R)
      hp hp1 (zero_lt_one.trans_le hq) rho)
    n hn a
  intro S _ pair first hfirst
  exact
    fkRectHorizontalCylinderDistinctPairedWitness_mass_le_pow_erase_of_planarization
      R pair hp hp1 hq ha (planarize pair) (htwo pair) S first hfirst



theorem fkRectHorizontalCylinderDistinctPairedWitness_mass_le_pow_erase_of_twoPoint
    (R : FKRectTorus) (pair : Fin R.width → Fin R.width)
    {p q a : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ha : 0 ≤ a)
    (htwo : ∀ (T : Finset (Fin R.width)) (hT : T.Nonempty)
        (x : Fin R.width) (hx : x ∉ T)
        (psi : ConfigSpace (Sym2 R.Vertex))
        (hbase : FKRectHorizontalCylinderDistinctPairedWitness R pair T psi)
        (hsource : ¬ FKRectHorizontalCylinderExploredVertex R psi T
          (x, fkRectBottomRow R))
        (htarget : ¬ FKRectHorizontalCylinderExploredVertex R psi T
          (pair x, fkRectTopRow R)),
      FK.infiniteTwoPointReal
        (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 (Site 2))))
        ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness
            R psi pair T hT hbase).embedding
          ⟨(x, fkRectBottomRow R), hsource⟩).1
        ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness
            R psi pair T hT hbase).embedding
          ⟨(pair x, fkRectTopRow R), htarget⟩).1 ≤ a)
    (S : Finset (Fin R.width)) (first : Fin R.width) (hfirst : first ∈ S) :
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectHorizontalCylinderGraph R) p q)
        {rho | FKRectHorizontalCylinderDistinctPairedWitness R pair S rho} ≤
      a ^ (S.erase first).card := by
  exact
    fkRectHorizontalCylinderDistinctPairedWitness_mass_le_pow_erase_of_planarization
      R pair hp hp1 hq ha
      (fun T hT psi hbase =>
        FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness
          R psi pair T hT hbase)
      htwo S first hfirst




theorem fkRectHorizontalCylinderCrossingTail_le_pow_pred_of_twoPoint
    (R : FKRectTorus) {p q a : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) (ha : 0 ≤ a)
    (htwo : ∀ (pair : Fin R.width → Fin R.width)
        (T : Finset (Fin R.width)) (hT : T.Nonempty)
        (x : Fin R.width) (hx : x ∉ T)
        (psi : ConfigSpace (Sym2 R.Vertex))
        (hbase : FKRectHorizontalCylinderDistinctPairedWitness R pair T psi)
        (hsource : ¬ FKRectHorizontalCylinderExploredVertex R psi T
          (x, fkRectBottomRow R))
        (htarget : ¬ FKRectHorizontalCylinderExploredVertex R psi T
          (pair x, fkRectTopRow R)),
      FK.infiniteTwoPointReal
        (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 (Site 2))))
        ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness
            R psi pair T hT hbase).embedding
          ⟨(x, fkRectBottomRow R), hsource⟩).1
        ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness
            R psi pair T hT hbase).embedding
          ⟨(pair x, fkRectTopRow R), htarget⟩).1 ≤ a)
    (n : Nat) (hn : 0 < n) :
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectHorizontalCylinderGraph R) p q)
        {rho | n ≤ fkRectHorizontalCylinderCrossingClusterCount R rho} ≤
      Nat.choose R.width n * R.width ^ R.width * a ^ (n - 1) := by
  apply fkRectHorizontalCylinderCrossingTail_le_choose_mul_pairCount_mul_pow_pred
    R (FK.fkProb (fkRectHorizontalCylinderGraph R) p q)
    (fun rho => FK.fkProb_nonneg (fkRectHorizontalCylinderGraph R)
      hp hp1 (zero_lt_one.trans_le hq) rho)
    n hn a
  intro S _ pair first hfirst
  exact
    fkRectHorizontalCylinderDistinctPairedWitness_mass_le_pow_erase_of_twoPoint
      R pair hp hp1 hq ha (htwo pair) S first hfirst

end

end StatMech.FrontierD

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectPrimalWitnessStep
import Code.Probability.AdaptiveFibreStep
import Code.FK.FKDisjointBoxDomainMarkov









open SimpleGraph

namespace StatMech.FrontierD

noncomputable section

open StatMech



def fkRectCutConfigOfFull (R : FKRectTorus)
    (rho : ConfigSpace (Sym2 R.Vertex)) : FKRectCutClosedConfig R :=
  (fkRectCutClosedEdgeConfigEquiv R).symm
    (FK.ecz_closeOff (fkRectCutGraph R) rho)

theorem fkRectFullGraphConfiguration_cutConfigOfFull
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) :
    fkRectFullGraphConfiguration R (fkRectCutConfigOfFull R rho).1 =
      (FK.ecz_closeOff (fkRectCutGraph R) rho).1 := by
  have h := (fkRectCutClosedEdgeConfigEquiv R).apply_symm_apply
    (FK.ecz_closeOff (fkRectCutGraph R) rho)
  exact congrArg Subtype.val h


theorem fkRectOpenGraph_cutConfigOfFull
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) :
    fkRectOpenGraph R (fkRectCutConfigOfFull R rho).1 =
      FK.openSub (fkRectCutGraph R) rho := by
  rw [← fkRectCut_openSub_eq R (fkRectCutConfigOfFull R rho)]
  have hequiv :
      (fkRectCutClosedEdgeConfigEquiv R (fkRectCutConfigOfFull R rho)).1 =
        (FK.ecz_closeOff (fkRectCutGraph R) rho).1 := by
    exact congrArg Subtype.val
      ((fkRectCutClosedEdgeConfigEquiv R).apply_symm_apply
        (FK.ecz_closeOff (fkRectCutGraph R) rho))
  rw [hequiv]
  symm
  apply FK.ecz_openSub_eq_of_edges
  intro e he
  exact (FK.ecz_closeOff_apply_edge (fkRectCutGraph R) rho he).symm



def FKRectPrimalFullExploredVertex
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) (v : R.Vertex) : Prop :=
  ∃ i ∈ S, (FK.openSub (fkRectCutGraph R) rho).Reachable
    (fkRectLeftColumn R, i) v



theorem fkRectPrimalFullExploredVertex_iff
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) (v : R.Vertex) :
    FKRectPrimalFullExploredVertex R S rho v ↔
      FKRectPrimalExploredVertex R S (fkRectCutConfigOfFull R rho).1 v := by
  have hclosed := (fkRectCutConfigOfFull R rho).2
  have hforce : fkRectForceCutClosed R (fkRectCutConfigOfFull R rho).1 =
      (fkRectCutConfigOfFull R rho).1 := hclosed
  unfold FKRectPrimalFullExploredVertex FKRectPrimalExploredVertex
  rw [hforce, fkRectOpenGraph_cutConfigOfFull]


theorem mem_fkRectPrimalUnexploredPairEdges_iff
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) (e : Sym2 R.Vertex) :
    e ∈ fkRectPrimalUnexploredPairEdges R S eta ↔
      ∃ x y : R.Vertex, e = s(x, y) ∧
        ¬ FKRectPrimalExploredVertex R S eta x ∧
        ¬ FKRectPrimalExploredVertex R S eta y := by
  rw [fkRectPrimalUnexploredPairEdges, FK.ocd_mem_innerEdgeFinset]
  constructor
  · rintro ⟨edge, rfl⟩
    induction edge using Sym2.ind with
    | _ x y =>
      exact ⟨x.1, y.1, FK.ocd_innerEdge_mk _ x y,
        x.2, y.2⟩
  · rintro ⟨x, y, rfl, hx, hy⟩
    let x' : FKRectPrimalUnexploredVertex R S eta := ⟨x, hx⟩
    let y' : FKRectPrimalUnexploredVertex R S eta := ⟨y, hy⟩
    refine ⟨s(x', y'), ?_⟩
    exact FK.ocd_innerEdge_mk _ x' y'


def fkRectPrimalFullUnexploredPairEdges
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) : Finset (Sym2 R.Vertex) := by
  classical
  exact Finset.univ.filter fun e =>
    ∃ x y : R.Vertex, e = s(x, y) ∧
      ¬ FKRectPrimalFullExploredVertex R S rho x ∧
      ¬ FKRectPrimalFullExploredVertex R S rho y

theorem mem_fkRectPrimalFullUnexploredPairEdges_iff
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) (e : Sym2 R.Vertex) :
    e ∈ fkRectPrimalFullUnexploredPairEdges R S rho ↔
      ∃ x y : R.Vertex, e = s(x, y) ∧
        ¬ FKRectPrimalFullExploredVertex R S rho x ∧
        ¬ FKRectPrimalFullExploredVertex R S rho y := by
  classical
  simp [fkRectPrimalFullUnexploredPairEdges]



theorem fkRectPrimalFullUnexploredPairEdges_eq_decoded
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) :
    fkRectPrimalFullUnexploredPairEdges R S rho =
      fkRectPrimalUnexploredPairEdges R S (fkRectCutConfigOfFull R rho).1 := by
  ext e
  rw [mem_fkRectPrimalFullUnexploredPairEdges_iff,
    mem_fkRectPrimalUnexploredPairEdges_iff]
  constructor
  · rintro ⟨x, y, he, hx, hy⟩
    exact ⟨x, y, he,
      fun h => hx ((fkRectPrimalFullExploredVertex_iff R S rho x).2 h),
      fun h => hy ((fkRectPrimalFullExploredVertex_iff R S rho y).2 h)⟩
  · rintro ⟨x, y, he, hx, hy⟩
    exact ⟨x, y, he,
      fun h => hx ((fkRectPrimalFullExploredVertex_iff R S rho x).1 h),
      fun h => hy ((fkRectPrimalFullExploredVertex_iff R S rho y).1 h)⟩



def fkRectPrimalAdaptiveInsideEdges
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) : Finset (Sym2 R.Vertex) :=
  fkRectPrimalFullUnexploredPairEdges R S rho


def fkRectPrimalAdaptiveProjection
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) : ConfigSpace (Sym2 R.Vertex) :=
  FK.projOff (fkRectPrimalAdaptiveInsideEdges R S rho) rho

theorem fkRectPrimalAdaptiveProjection_le
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) :
    fkRectPrimalAdaptiveProjection R S rho ≤ rho := by
  intro e
  unfold fkRectPrimalAdaptiveProjection FK.projOff
  by_cases he : e ∈ fkRectPrimalAdaptiveInsideEdges R S rho
  · simp [he]
  · simp [he]

theorem fkRectPrimalAdaptiveProjection_eq_of_not_mem
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) {e : Sym2 R.Vertex}
    (he : e ∉ fkRectPrimalAdaptiveInsideEdges R S rho) :
    fkRectPrimalAdaptiveProjection R S rho e = rho e := by
  unfold fkRectPrimalAdaptiveProjection FK.projOff
  simp [he]


theorem not_mem_fkRectPrimalFullUnexploredPairEdges_of_explored_left
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) {x y : R.Vertex}
    (hx : FKRectPrimalFullExploredVertex R S rho x) :
    s(x, y) ∉ fkRectPrimalFullUnexploredPairEdges R S rho := by
  intro hmem
  rcases (mem_fkRectPrimalFullUnexploredPairEdges_iff R S rho _).1 hmem with
    ⟨u, v, huv, hu, hv⟩
  rcases Sym2.eq_iff.mp huv with ⟨hxu, _⟩ | ⟨hxv, _⟩
  · exact hu (hxu ▸ hx)
  · exact hv (hxv ▸ hx)



theorem fkRectPrimalAdaptiveProjection_openAdj_of_explored
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) {x y : R.Vertex}
    (hx : FKRectPrimalFullExploredVertex R S rho x)
    (hxy : (FK.openSub (fkRectCutGraph R) rho).Adj x y) :
    (FK.openSub (fkRectCutGraph R)
      (fkRectPrimalAdaptiveProjection R S rho)).Adj x y := by
  refine ⟨hxy.1, ?_⟩
  have hpair : s(x, y) ∉ fkRectPrimalFullUnexploredPairEdges R S rho :=
    not_mem_fkRectPrimalFullUnexploredPairEdges_of_explored_left
      R S rho hx
  have hinside : s(x, y) ∉ fkRectPrimalAdaptiveInsideEdges R S rho := by
    exact hpair
  rw [fkRectPrimalAdaptiveProjection_eq_of_not_mem R S rho hinside]
  exact hxy.2


theorem fkRectPrimalFullExploredVertex_projection_of_explored
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) {v : R.Vertex}
    (hv : FKRectPrimalFullExploredVertex R S rho v) :
    FKRectPrimalFullExploredVertex R S
      (fkRectPrimalAdaptiveProjection R S rho) v := by
  rcases hv with ⟨i, hi, hreach⟩
  refine ⟨i, hi, ?_⟩
  let source : R.Vertex := (fkRectLeftColumn R, i)
  let G := FK.openSub (fkRectCutGraph R) rho
  let H := FK.openSub (fkRectCutGraph R)
    (fkRectPrimalAdaptiveProjection R S rho)
  let liftWalk : ∀ {x y : R.Vertex}, G.Walk x y →
      G.Reachable source x → H.Walk x y := by
    intro x y path
    induction path with
    | nil => intro _; exact SimpleGraph.Walk.nil
    | @cons x y z hxy path ih =>
        intro hsx
        exact SimpleGraph.Walk.cons
          (fkRectPrimalAdaptiveProjection_openAdj_of_explored R S rho
            ⟨i, hi, hsx⟩ hxy)
          (ih (hsx.trans hxy.reachable))
  exact hreach.elim fun path =>
    ⟨liftWalk path (SimpleGraph.Reachable.refl source)⟩


theorem fkRectPrimalFullExploredVertex_of_projection
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) {v : R.Vertex}
    (hv : FKRectPrimalFullExploredVertex R S
      (fkRectPrimalAdaptiveProjection R S rho) v) :
    FKRectPrimalFullExploredVertex R S rho v := by
  rcases hv with ⟨i, hi, hreach⟩
  exact ⟨i, hi, hreach.mono (FK.openSub_mono _
    (fkRectPrimalAdaptiveProjection_le R S rho))⟩


theorem fkRectPrimalFullExploredVertex_projection_iff
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) (v : R.Vertex) :
    FKRectPrimalFullExploredVertex R S
        (fkRectPrimalAdaptiveProjection R S rho) v ↔
      FKRectPrimalFullExploredVertex R S rho v :=
  ⟨fkRectPrimalFullExploredVertex_of_projection R S rho,
    fkRectPrimalFullExploredVertex_projection_of_explored R S rho⟩

theorem fkRectPrimalAdaptiveInsideEdges_projection
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) :
    fkRectPrimalAdaptiveInsideEdges R S
        (fkRectPrimalAdaptiveProjection R S rho) =
      fkRectPrimalAdaptiveInsideEdges R S rho := by
  unfold fkRectPrimalAdaptiveInsideEdges
  ext e
  rw [mem_fkRectPrimalFullUnexploredPairEdges_iff,
    mem_fkRectPrimalFullUnexploredPairEdges_iff]
  constructor
  · rintro ⟨x, y, he, hx, hy⟩
    exact ⟨x, y, he,
      fun h => hx ((fkRectPrimalFullExploredVertex_projection_iff R S rho x).2 h),
      fun h => hy ((fkRectPrimalFullExploredVertex_projection_iff R S rho y).2 h)⟩
  · rintro ⟨x, y, he, hx, hy⟩
    exact ⟨x, y, he,
      fun h => hx ((fkRectPrimalFullExploredVertex_projection_iff R S rho x).1 h),
      fun h => hy ((fkRectPrimalFullExploredVertex_projection_iff R S rho y).1 h)⟩


theorem fkRectPrimalAdaptiveProjection_idem
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) :
    fkRectPrimalAdaptiveProjection R S
        (fkRectPrimalAdaptiveProjection R S rho) =
      fkRectPrimalAdaptiveProjection R S rho := by
  change FK.projOff
      (fkRectPrimalAdaptiveInsideEdges R S
        (fkRectPrimalAdaptiveProjection R S rho))
      (fkRectPrimalAdaptiveProjection R S rho) =
    fkRectPrimalAdaptiveProjection R S rho
  rw [fkRectPrimalAdaptiveInsideEdges_projection]
  unfold fkRectPrimalAdaptiveProjection
  exact FK.projOff_idem _ _


def FKRectPrimalFullCrossingSource
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (i : Fin R.height) : Prop :=
  ∃ z : Fin R.height,
    (FK.openSub (fkRectCutGraph R) rho).Reachable
      (fkRectLeftColumn R, i) (fkRectRightColumn R, z)



def FKRectPrimalFullDistinctCrossingWitness
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) : Prop :=
  (∀ i ∈ S, FKRectPrimalFullCrossingSource R rho i) ∧
  (∀ i ∈ S, ∀ j ∈ S, i ≠ j →
    ¬ (FK.openSub (fkRectCutGraph R) rho).Reachable
      (fkRectLeftColumn R, i) (fkRectLeftColumn R, j))



theorem fkRectPrimalSourceReachable_projection_iff
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex))
    {i : Fin R.height} (hi : i ∈ S) (v : R.Vertex) :
    (FK.openSub (fkRectCutGraph R)
        (fkRectPrimalAdaptiveProjection R S rho)).Reachable
        (fkRectLeftColumn R, i) v ↔
      (FK.openSub (fkRectCutGraph R) rho).Reachable
        (fkRectLeftColumn R, i) v := by
  constructor
  · intro hreach
    exact hreach.mono (FK.openSub_mono _
      (fkRectPrimalAdaptiveProjection_le R S rho))
  · intro hreach
    let source : R.Vertex := (fkRectLeftColumn R, i)
    let G := FK.openSub (fkRectCutGraph R) rho
    let H := FK.openSub (fkRectCutGraph R)
      (fkRectPrimalAdaptiveProjection R S rho)
    let liftWalk : ∀ {x y : R.Vertex}, G.Walk x y →
        G.Reachable source x → H.Walk x y := by
      intro x y path
      induction path with
      | nil => intro _; exact SimpleGraph.Walk.nil
      | @cons x y z hxy path ih =>
          intro hsx
          exact SimpleGraph.Walk.cons
            (fkRectPrimalAdaptiveProjection_openAdj_of_explored R S rho
              ⟨i, hi, hsx⟩ hxy)
            (ih (hsx.trans hxy.reachable))
    exact hreach.elim fun path =>
      ⟨liftWalk path (SimpleGraph.Reachable.refl source)⟩


theorem fkRectPrimalFullDistinctCrossingWitness_projection_iff
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) :
    FKRectPrimalFullDistinctCrossingWitness R S
        (fkRectPrimalAdaptiveProjection R S rho) ↔
      FKRectPrimalFullDistinctCrossingWitness R S rho := by
  constructor
  · rintro ⟨hcross, hdistinct⟩
    constructor
    · intro i hi
      rcases hcross i hi with ⟨z, hiz⟩
      exact ⟨z,
        (fkRectPrimalSourceReachable_projection_iff R S rho hi _).1 hiz⟩
    · intro i hi j hj hij hreach
      apply hdistinct i hi j hj hij
      exact (fkRectPrimalSourceReachable_projection_iff R S rho hi _).2 hreach
  · rintro ⟨hcross, hdistinct⟩
    constructor
    · intro i hi
      rcases hcross i hi with ⟨z, hiz⟩
      exact ⟨z,
        (fkRectPrimalSourceReachable_projection_iff R S rho hi _).2 hiz⟩
    · intro i hi j hj hij hreach
      apply hdistinct i hi j hj hij
      exact (fkRectPrimalSourceReachable_projection_iff R S rho hi _).1 hreach



theorem fkRectPrimalFullDistinctCrossingWitness_fibre_iff
    (R : FKRectTorus) (S : Finset (Fin R.height))
    {rho sigma : ConfigSpace (Sym2 R.Vertex)}
    (hproj : fkRectPrimalAdaptiveProjection R S rho =
      fkRectPrimalAdaptiveProjection R S sigma) :
    FKRectPrimalFullDistinctCrossingWitness R S rho ↔
      FKRectPrimalFullDistinctCrossingWitness R S sigma := by
  rw [← fkRectPrimalFullDistinctCrossingWitness_projection_iff R S rho,
    ← fkRectPrimalFullDistinctCrossingWitness_projection_iff R S sigma,
    hproj]



theorem fkRectPrimalSourceReachable_agreesOff_iff
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (psi rho : ConfigSpace (Sym2 R.Vertex))
    (hagree : FK.AgreesOff
      (fkRectPrimalAdaptiveInsideEdges R S psi) psi rho)
    {i : Fin R.height} (hi : i ∈ S) (v : R.Vertex) :
    (FK.openSub (fkRectCutGraph R) psi).Reachable
        (fkRectLeftColumn R, i) v ↔
      (FK.openSub (fkRectCutGraph R) rho).Reachable
        (fkRectLeftColumn R, i) v := by
  let source : R.Vertex := (fkRectLeftColumn R, i)
  let Gpsi := FK.openSub (fkRectCutGraph R) psi
  let Grho := FK.openSub (fkRectCutGraph R) rho
  have transfer : ∀ {x y : R.Vertex},
      FKRectPrimalFullExploredVertex R S psi x →
      (Gpsi.Adj x y ↔ Grho.Adj x y) := by
    intro x y hx
    have hnot : s(x, y) ∉ fkRectPrimalAdaptiveInsideEdges R S psi :=
      not_mem_fkRectPrimalFullUnexploredPairEdges_of_explored_left
        R S psi hx
    have heq := hagree s(x, y) hnot
    constructor
    · rintro ⟨hadj, hopen⟩
      exact ⟨hadj, heq.symm ▸ hopen⟩
    · rintro ⟨hadj, hopen⟩
      exact ⟨hadj, heq ▸ hopen⟩
  constructor
  · intro hreach
    let liftWalk : ∀ {x y : R.Vertex}, Gpsi.Walk x y →
        Gpsi.Reachable source x → Grho.Walk x y := by
      intro x y path
      induction path with
      | nil => intro _; exact SimpleGraph.Walk.nil
      | @cons x y z hxy path ih =>
          intro hsx
          exact SimpleGraph.Walk.cons
            ((transfer ⟨i, hi, hsx⟩).1 hxy)
            (ih (hsx.trans hxy.reachable))
    exact hreach.elim fun path =>
      ⟨liftWalk path (SimpleGraph.Reachable.refl source)⟩
  · intro hreach
    let liftWalk : ∀ {x y : R.Vertex}, Grho.Walk x y →
        Gpsi.Reachable source x → Gpsi.Walk x y := by
      intro x y path
      induction path with
      | nil => intro _; exact SimpleGraph.Walk.nil
      | @cons x y z hxy path ih =>
          intro hsx
          have hxyPsi := (transfer ⟨i, hi, hsx⟩).2 hxy
          exact SimpleGraph.Walk.cons hxyPsi
            (ih (hsx.trans hxyPsi.reachable))
    exact hreach.elim fun path =>
      ⟨liftWalk path (SimpleGraph.Reachable.refl source)⟩

theorem fkRectPrimalFullExploredVertex_agreesOff_iff
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (psi rho : ConfigSpace (Sym2 R.Vertex))
    (hagree : FK.AgreesOff
      (fkRectPrimalAdaptiveInsideEdges R S psi) psi rho)
    (v : R.Vertex) :
    FKRectPrimalFullExploredVertex R S psi v ↔
      FKRectPrimalFullExploredVertex R S rho v := by
  constructor
  · rintro ⟨i, hi, hiv⟩
    exact ⟨i, hi,
      (fkRectPrimalSourceReachable_agreesOff_iff
        R S psi rho hagree hi v).1 hiv⟩
  · rintro ⟨i, hi, hiv⟩
    exact ⟨i, hi,
      (fkRectPrimalSourceReachable_agreesOff_iff
        R S psi rho hagree hi v).2 hiv⟩

theorem fkRectPrimalAdaptiveInsideEdges_eq_of_agreesOff
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (psi rho : ConfigSpace (Sym2 R.Vertex))
    (hagree : FK.AgreesOff
      (fkRectPrimalAdaptiveInsideEdges R S psi) psi rho) :
    fkRectPrimalAdaptiveInsideEdges R S rho =
      fkRectPrimalAdaptiveInsideEdges R S psi := by
  unfold fkRectPrimalAdaptiveInsideEdges
  ext e
  rw [mem_fkRectPrimalFullUnexploredPairEdges_iff,
    mem_fkRectPrimalFullUnexploredPairEdges_iff]
  constructor
  · rintro ⟨x, y, he, hx, hy⟩
    exact ⟨x, y, he,
      fun h => hx ((fkRectPrimalFullExploredVertex_agreesOff_iff
        R S psi rho hagree x).1 h),
      fun h => hy ((fkRectPrimalFullExploredVertex_agreesOff_iff
        R S psi rho hagree y).1 h)⟩
  · rintro ⟨x, y, he, hx, hy⟩
    exact ⟨x, y, he,
      fun h => hx ((fkRectPrimalFullExploredVertex_agreesOff_iff
        R S psi rho hagree x).2 h),
      fun h => hy ((fkRectPrimalFullExploredVertex_agreesOff_iff
        R S psi rho hagree y).2 h)⟩



theorem fkRectPrimalAdaptiveProjection_filter_eq_condFibre
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (psi : ConfigSpace (Sym2 R.Vertex))
    (hpsi : fkRectPrimalAdaptiveProjection R S psi = psi) :
    Finset.univ.filter
        (fun rho => fkRectPrimalAdaptiveProjection R S rho = psi) =
      FK.condFibre (fkRectPrimalAdaptiveInsideEdges R S psi) psi := by
  ext rho
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, FK.mem_condFibre]
  constructor
  · intro hproj
    have hF : fkRectPrimalAdaptiveInsideEdges R S rho =
        fkRectPrimalAdaptiveInsideEdges R S psi := by
      rw [← fkRectPrimalAdaptiveInsideEdges_projection R S rho, hproj]
    intro e he
    have hval := congrFun hproj e
    have hnotRho : e ∉ fkRectPrimalAdaptiveInsideEdges R S rho := by
      rwa [hF]
    rw [← hval]
    exact (fkRectPrimalAdaptiveProjection_eq_of_not_mem
      R S rho hnotRho).symm
  · intro hagree
    have hF := fkRectPrimalAdaptiveInsideEdges_eq_of_agreesOff
      R S psi rho hagree
    unfold fkRectPrimalAdaptiveProjection
    rw [hF]
    have hproj := FK.projOff_eq_of_agreesOff hagree
    rw [hproj]
    simpa [fkRectPrimalAdaptiveProjection] using hpsi




def FKRectPrimalAdaptiveArmEvent
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (i : Fin R.height) (psi : ConfigSpace (Sym2 R.Vertex)) :
    Set (ConfigSpace (Sym2 R.Vertex)) :=
  {rho | ∃ hsource : ¬ FKRectPrimalFullExploredVertex R S psi
      (fkRectLeftColumn R, i),
    let source : FKRectPrimalUnexploredVertex R S
        (fkRectCutConfigOfFull R psi).1 :=
      ⟨(fkRectLeftColumn R, i), fun h => hsource
        ((fkRectPrimalFullExploredVertex_iff R S psi _).2 h)⟩
    FK.ocd_innerRestrict
        (Subtype.val : FKRectPrimalUnexploredVertex R S
          (fkRectCutConfigOfFull R psi).1 → R.Vertex) rho ∈
      FKRectPrimalUnexploredRightArmEvent R S
        (fkRectCutConfigOfFull R psi).1 source}



theorem fkRectPrimalFullDistinctCrossingWitness_insert_not_explored_of_reachable
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (i : Fin R.height) (hi : i ∉ S)
    (rho : ConfigSpace (Sym2 R.Vertex))
    (h : FKRectPrimalFullDistinctCrossingWitness R (insert i S) rho)
    {v : R.Vertex}
    (hiv : (FK.openSub (fkRectCutGraph R) rho).Reachable
      (fkRectLeftColumn R, i) v) :
    ¬ FKRectPrimalFullExploredVertex R S rho v := by
  rintro ⟨j, hj, hjv⟩
  apply h.2 i (Finset.mem_insert_self i S)
    j (Finset.mem_insert_of_mem hj) (fun hij => hi (hij ▸ hj))
  exact hiv.trans hjv.symm



theorem fkRectPrimalFullDistinctCrossingWitness_insert_imp_adaptiveArm
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (i : Fin R.height) (hi : i ∉ S)
    (rho : ConfigSpace (Sym2 R.Vertex))
    (h : FKRectPrimalFullDistinctCrossingWitness R (insert i S) rho) :
    rho ∈ FKRectPrimalAdaptiveArmEvent R S i
      (fkRectPrimalAdaptiveProjection R S rho) := by
  let psi := fkRectPrimalAdaptiveProjection R S rho
  have hsourceRho :=
    fkRectPrimalFullDistinctCrossingWitness_insert_not_explored_of_reachable
      R S i hi rho h
        (SimpleGraph.Reachable.refl (fkRectLeftColumn R, i))
  have hsourcePsi : ¬ FKRectPrimalFullExploredVertex R S psi
      (fkRectLeftColumn R, i) := by
    intro hexplored
    exact hsourceRho
      ((fkRectPrimalFullExploredVertex_projection_iff R S rho _).1 hexplored)
  let eta := fkRectCutConfigOfFull R psi
  let source : FKRectPrimalUnexploredVertex R S eta.1 :=
    ⟨(fkRectLeftColumn R, i), fun hidx => hsourcePsi
      ((fkRectPrimalFullExploredVertex_iff R S psi _).2 hidx)⟩
  rcases h.1 i (Finset.mem_insert_self i S) with ⟨z, hiz⟩
  have hnotPsi : ∀ {v : R.Vertex},
      (FK.openSub (fkRectCutGraph R) rho).Reachable
          (fkRectLeftColumn R, i) v →
        ¬ FKRectPrimalFullExploredVertex R S psi v := by
    intro v hiv hexplored
    have hexploredRho : FKRectPrimalFullExploredVertex R S rho v :=
      (fkRectPrimalFullExploredVertex_projection_iff R S rho v).1 hexplored
    exact fkRectPrimalFullDistinctCrossingWitness_insert_not_explored_of_reachable
      R S i hi rho h hiv hexploredRho
  let target : FKRectPrimalUnexploredVertex R S eta.1 :=
    ⟨(fkRectRightColumn R, z), fun hidx => hnotPsi hiz
      ((fkRectPrimalFullExploredVertex_iff R S psi _).2 hidx)⟩
  have hreach :
      (FK.openSub (fkRectPrimalUnexploredInducedGraph R S eta.1)
        (FK.ocd_innerRestrict
          (Subtype.val : FKRectPrimalUnexploredVertex R S eta.1 → R.Vertex)
          rho)).Reachable source target := by
    let G := FK.openSub (fkRectCutGraph R) rho
    let H := FK.openSub (fkRectPrimalUnexploredInducedGraph R S eta.1)
      (FK.ocd_innerRestrict
        (Subtype.val : FKRectPrimalUnexploredVertex R S eta.1 → R.Vertex)
        rho)
    let liftWalk : ∀ {x y : R.Vertex} (path : G.Walk x y)
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
            constructor
            · exact hxy.1
            · simpa [FK.ocd_innerRestrict, FK.ocd_innerEdge_mk] using hxy.2
          exact SimpleGraph.Walk.cons hstep
            (ih (hsx.trans hxy.reachable))
    exact hiz.elim fun path =>
      ⟨by simpa only [source, target, G, H] using
        liftWalk path (SimpleGraph.Reachable.refl (fkRectLeftColumn R, i))⟩
  exact ⟨hsourcePsi, ⟨target, rfl, hreach⟩⟩



theorem fkRectPrimalFullDistinctCrossingWitness_insert_imp_base
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (i : Fin R.height) (rho : ConfigSpace (Sym2 R.Vertex))
    (h : FKRectPrimalFullDistinctCrossingWitness R (insert i S) rho) :
    FKRectPrimalFullDistinctCrossingWitness R S rho := by
  rcases h with ⟨hcross, hdistinct⟩
  exact ⟨fun j hj => hcross j (Finset.mem_insert_of_mem hj),
    fun j hj k hk hjk => hdistinct j (Finset.mem_insert_of_mem hj)
      k (Finset.mem_insert_of_mem hk) hjk⟩



theorem fkRectPrimalFullDistinctCrossingWitness_insert_source_not_explored
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (i : Fin R.height) (hi : i ∉ S)
    (rho : ConfigSpace (Sym2 R.Vertex))
    (h : FKRectPrimalFullDistinctCrossingWitness R (insert i S) rho) :
    ¬ FKRectPrimalFullExploredVertex R S rho (fkRectLeftColumn R, i) := by
  rintro ⟨j, hj, hji⟩
  exact h.2 i (Finset.mem_insert_self i S)
    j (Finset.mem_insert_of_mem hj) (fun hij => hi (hij ▸ hj)) hji.symm

private instance instDecidableFalseBoundaryAdaptive (R : FKRectTorus) :
    DecidablePred (fun _ : R.Vertex => False) :=
  fun _ => isFalse id



theorem fkRectPrimalAdaptive_condRightArm_le_boxBdry
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (psi : ConfigSpace (Sym2 R.Vertex))
    (source : FKRectPrimalUnexploredVertex R S
      (fkRectCutConfigOfFull R psi).1)
    (hleft : source.1.1 = fkRectLeftColumn R)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (∑ rho : ConfigSpace (Sym2 R.Vertex),
        (FK.ocd_innerRestrict
          (Subtype.val : FKRectPrimalUnexploredVertex R S
            (fkRectCutConfigOfFull R psi).1 → R.Vertex) ⁻¹'
          FKRectPrimalUnexploredRightArmEvent R S
            (fkRectCutConfigOfFull R psi).1 source).indicator
              (fun _ => (1 : Real)) rho *
          FK.condBcProb (fkRectCutGraph R)
            (StatMech.Lattice.boundaryCliqueGraph
              (fun _ : R.Vertex => False)) p q
            (fkRectPrimalFullUnexploredPairEdges R S psi) psi rho) ≤
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        MeasureTheory.Measure (ConfigSpace
          (Sym2 (StatMech.Lattice.Site 2)))).real
        (FK.boxBdryConnEvent 2 (R.width - 2)) := by
  let eta := fkRectCutConfigOfFull R psi
  let iota :=
    (Subtype.val : FKRectPrimalUnexploredVertex R S eta.1 → R.Vertex)
  let psi0 := fkRectFullGraphConfiguration R eta.1
  let A := FKRectPrimalUnexploredRightArmEvent R S eta.1 source
  have hforce : fkRectForceCutClosed R eta.1 = eta.1 := eta.2
  have hbot0 := fkRectPrimalExploration_ocdInducedWiring_eq_bot R S eta.1
  rw [hforce] at hbot0
  have hedgeEq : ∀ x y : R.Vertex, (fkRectCutGraph R).Adj x y →
      psi s(x, y) = psi0 s(x, y) := by
    intro x y hxy
    have hedge : s(x, y) ∈ (fkRectCutGraph R).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset]
      exact hxy
    have hclose := FK.ecz_closeOff_apply_edge
      (fkRectCutGraph R) psi hedge
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
    hp hp1 (zero_lt_one.trans_le hq) psi
    (fun omega => FK.fkProb
      (fkRectPrimalUnexploredInducedGraph R S eta.1) p q omega)
    (fun omega => by
      have hdm := FK.ocd_condBcProb_psiExt_eq_bcProb
        (Gin := fkRectPrimalUnexploredInducedGraph R S eta.1)
        (Gout := fkRectCutGraph R)
        (ιV := iota) (bdryOut := fun _ : R.Vertex => False)
        Subtype.val_injective
        (fkRectPrimalUnexploredInducedGraph_adjMatch R S eta.1)
        hp hp1 (zero_lt_one.trans_le hq) psi omega
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
  have hF : fkRectPrimalFullUnexploredPairEdges R S psi =
      fkRectPrimalUnexploredPairEdges R S eta.1 :=
    fkRectPrimalFullUnexploredPairEdges_eq_decoded R S psi
  rw [hF]
  change _ ≤ _
  rw [show (∑ rho : ConfigSpace (Sym2 R.Vertex),
      (FK.ocd_innerRestrict iota ⁻¹' A).indicator
          (fun _ => (1 : Real)) rho *
        FK.condBcProb (fkRectCutGraph R)
          (StatMech.Lattice.boundaryCliqueGraph
            (fun _ : R.Vertex => False)) p q
          (fkRectPrimalUnexploredPairEdges R S eta.1) psi rho) =
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        FK.fkProb (fkRectPrimalUnexploredInducedGraph R S eta.1)
          p q omega by exact hevent]
  exact fkRectPrimalUnexploredRightArm_freeMass_le_boxBdry
    R S eta.1 source hleft hp hp1 hq


theorem fkRectPrimalAdaptiveArmEvent_condMass_le_boxBdry
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (i : Fin R.height) (psi : ConfigSpace (Sym2 R.Vertex))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (∑ rho : ConfigSpace (Sym2 R.Vertex),
        (FKRectPrimalAdaptiveArmEvent R S i psi).indicator
            (fun _ => (1 : Real)) rho *
          FK.condBcProb (fkRectCutGraph R)
            (StatMech.Lattice.boundaryCliqueGraph
              (fun _ : R.Vertex => False)) p q
            (fkRectPrimalAdaptiveInsideEdges R S psi) psi rho) ≤
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        MeasureTheory.Measure (ConfigSpace
          (Sym2 (StatMech.Lattice.Site 2)))).real
        (FK.boxBdryConnEvent 2 (R.width - 2)) := by
  by_cases hsource : FKRectPrimalFullExploredVertex R S psi
      (fkRectLeftColumn R, i)
  · have hempty : FKRectPrimalAdaptiveArmEvent R S i psi = ∅ := by
      ext rho
      constructor
      · rintro ⟨hnot, _⟩
        exact (hnot hsource).elim
      · simp
    rw [hempty]
    simp only [Set.indicator_empty, zero_mul, Finset.sum_const_zero]
    exact MeasureTheory.measureReal_nonneg
  · let source : FKRectPrimalUnexploredVertex R S
        (fkRectCutConfigOfFull R psi).1 :=
      ⟨(fkRectLeftColumn R, i), fun h => hsource
        ((fkRectPrimalFullExploredVertex_iff R S psi _).2 h)⟩
    have hevent : FKRectPrimalAdaptiveArmEvent R S i psi =
        FK.ocd_innerRestrict
          (Subtype.val : FKRectPrimalUnexploredVertex R S
            (fkRectCutConfigOfFull R psi).1 → R.Vertex) ⁻¹'
          FKRectPrimalUnexploredRightArmEvent R S
            (fkRectCutConfigOfFull R psi).1 source := by
      ext rho
      constructor
      · rintro ⟨hnot, harm⟩
        simpa only [source] using harm
      · intro harm
        exact ⟨hsource, by simpa only [source] using harm⟩
    rw [hevent]
    exact fkRectPrimalAdaptive_condRightArm_le_boxBdry
      R S psi source rfl hp hp1 hq



theorem fkRectPrimalFullDistinctCrossingWitness_step
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (i : Fin R.height) (hi : i ∉ S)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectCutGraph R) p q)
        {rho | FKRectPrimalFullDistinctCrossingWitness R (insert i S) rho} ≤
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        MeasureTheory.Measure (ConfigSpace
          (Sym2 (StatMech.Lattice.Site 2)))).real
          (FK.boxBdryConnEvent 2 (R.width - 2)) *
        StatMech.Probability.finiteEventMass
          (FK.fkProb (fkRectCutGraph R) p q)
          {rho | FKRectPrimalFullDistinctCrossingWitness R S rho} := by
  classical
  let P := fkRectPrimalAdaptiveProjection R S
  let Base : Set (ConfigSpace (Sym2 R.Vertex)) :=
    {rho | FKRectPrimalFullDistinctCrossingWitness R S rho}
  let Inserted : Set (ConfigSpace (Sym2 R.Vertex)) :=
    {rho | FKRectPrimalFullDistinctCrossingWitness R (insert i S) rho}
  let Arm : ConfigSpace (Sym2 R.Vertex) →
      Set (ConfigSpace (Sym2 R.Vertex)) :=
    fun psi => FKRectPrimalAdaptiveArmEvent R S i psi
  let a := (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
    MeasureTheory.Measure (ConfigSpace
      (Sym2 (StatMech.Lattice.Site 2)))).real
      (FK.boxBdryConnEvent 2 (R.width - 2))
  apply StatMech.Probability.finiteEventMass_adaptive_fibre_step
    (FK.fkProb (fkRectCutGraph R) p q)
    (fun rho => FK.fkProb_nonneg (fkRectCutGraph R)
      hp hp1 (zero_lt_one.trans_le hq) rho)
    P
    (fun rho => fkRectPrimalAdaptiveProjection_idem R S rho)
    Base Inserted Arm
  · intro rho sigma hproj
    exact fkRectPrimalFullDistinctCrossingWitness_fibre_iff
      R S hproj
  · intro rho hrho
    exact ⟨fkRectPrimalFullDistinctCrossingWitness_insert_imp_base
        R S i rho hrho,
      fkRectPrimalFullDistinctCrossingWitness_insert_imp_adaptiveArm
        R S i hi rho hrho⟩
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
        FK.condBcProb (fkRectCutGraph R)
          (⊥ : SimpleGraph R.Vertex) p q F psi rho
    have hfilter : Finset.univ.filter (fun rho => P rho = psi) =
        FK.condFibre F psi := by
      exact fkRectPrimalAdaptiveProjection_filter_eq_condFibre
        R S psi hfixed
    have hraw := FK.bcProb_event_fibre_eq_mass_mul_cond
      (fkRectCutGraph R) (⊥ : SimpleGraph R.Vertex)
      hp hp1 (zero_lt_one.trans_le hq) F psi (Arm psi)
    simp_rw [FK.bcProb_bot_eq_fkProb] at hraw
    have hboundary : StatMech.Lattice.boundaryCliqueGraph
        (fun _ : R.Vertex => False) = (⊥ : SimpleGraph R.Vertex) := by
      apply SimpleGraph.ext
      ext x y
      rw [StatMech.Lattice.boundaryCliqueGraph_adj]
      simp [SimpleGraph.bot_adj]
    have hcond : C ≤ a := by
      simpa [C, a, hboundary] using
        fkRectPrimalAdaptiveArmEvent_condMass_le_boxBdry
          R S i psi hp hp1 hq
    have hM : 0 ≤ M := by
      exact Finset.sum_nonneg fun sigma _ =>
        FK.fkProb_nonneg (fkRectCutGraph R)
          hp hp1 (zero_lt_one.trans_le hq) sigma
    have hind : ∀ omega : ConfigSpace (Sym2 R.Vertex),
        (Arm psi).indicator (FK.fkProb (fkRectCutGraph R) p q) omega =
          FK.fkProb (fkRectCutGraph R) p q omega *
            (Arm psi).indicator (fun _ => (1 : Real)) omega := by
      intro omega
      by_cases hArm : omega ∈ Arm psi <;> simp [hArm]
    calc
      (∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          (Arm psi).indicator (FK.fkProb (fkRectCutGraph R) p q) omega) =
        M * C := by
          rw [hfilter]
          simp_rw [hind]
          simpa [M, C, mul_comm] using hraw
      _ ≤ M * a := mul_le_mul_of_nonneg_left hcond hM
      _ = a * M := by ring
      _ = a * ∑ omega ∈
          (Finset.univ.filter fun omega => P omega = psi),
            FK.fkProb (fkRectCutGraph R) p q omega := by rw [hfilter]


def FKRectPrimalStableCrossingWitnessCore
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) : Prop :=
  FKRectPrimalFullDistinctCrossingWitness R S
    (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))

theorem fkRectPrimalFullDistinctCrossingWitness_congr_openSub
    (R : FKRectTorus) (S : Finset (Fin R.height))
    {rho sigma : ConfigSpace (Sym2 R.Vertex)}
    (hgraph : FK.openSub (fkRectCutGraph R) rho =
      FK.openSub (fkRectCutGraph R) sigma) :
    FKRectPrimalFullDistinctCrossingWitness R S rho ↔
      FKRectPrimalFullDistinctCrossingWitness R S sigma := by
  unfold FKRectPrimalFullDistinctCrossingWitness
    FKRectPrimalFullCrossingSource
  rw [hgraph]

theorem fkRectPrimalStableCrossingWitness_cutConfigOfFull_iff
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) :
    FKRectPrimalStableCrossingWitnessCore R S
        (fkRectCutConfigOfFull R rho).1 ↔
      FKRectPrimalFullDistinctCrossingWitness R S rho := by
  unfold FKRectPrimalStableCrossingWitnessCore
  have hforce : fkRectForceCutClosed R (fkRectCutConfigOfFull R rho).1 =
      (fkRectCutConfigOfFull R rho).1 := (fkRectCutConfigOfFull R rho).2
  rw [hforce]
  apply fkRectPrimalFullDistinctCrossingWitness_congr_openSub
  calc
    FK.openSub (fkRectCutGraph R)
        (fkRectFullGraphConfiguration R (fkRectCutConfigOfFull R rho).1) =
      fkRectOpenGraph R (fkRectCutConfigOfFull R rho).1 :=
        fkRectCut_openSub_eq R (fkRectCutConfigOfFull R rho)
    _ = FK.openSub (fkRectCutGraph R) rho :=
      fkRectOpenGraph_cutConfigOfFull R rho



theorem fkRectCutGraph_stableWitnessEvent_eq
    (R : FKRectTorus) (S : Finset (Fin R.height)) :
    FK.ecz_closeOff (fkRectCutGraph R) ⁻¹'
        fkRectCutEdgeEvent R
          {eta | FKRectPrimalStableCrossingWitnessCore R S eta} =
      {rho | FKRectPrimalFullDistinctCrossingWitness R S rho} := by
  ext rho
  change FKRectPrimalStableCrossingWitnessCore R S
      ((fkRectCutClosedEdgeConfigEquiv R).symm
        (FK.ecz_closeOff (fkRectCutGraph R) rho)).1 ↔ _
  exact fkRectPrimalStableCrossingWitness_cutConfigOfFull_iff R S rho



theorem fkRectCriticalCutFree_stableWitness_eq_finiteEventMass
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (S : Finset (Fin R.height)) :
    fkRectCriticalCutFreeEventMass R q
        {eta | FKRectPrimalStableCrossingWitnessCore R S eta} =
      StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectCutGraph R) (fkRectCriticalP q) q)
        {rho | FKRectPrimalFullDistinctCrossingWitness R S rho} := by
  rw [fkRectCriticalCutFreeEventMass_eq_cutGraph R hq,
    fkRectCutGraph_stableWitnessEvent_eq]
  unfold StatMech.Probability.finiteEventMass
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hmem : FKRectPrimalFullDistinctCrossingWitness R S rho
  · have hs : rho ∈
        {rho | FKRectPrimalFullDistinctCrossingWitness R S rho} := hmem
    simp [Set.indicator, hs]
  · have hs : rho ∉
        {rho | FKRectPrimalFullDistinctCrossingWitness R S rho} := hmem
    simp [Set.indicator, hs]



theorem fkRectCriticalCutFree_stableWitness_step
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (S : Finset (Fin R.height)) (i : Fin R.height) (hi : i ∉ S) :
    fkRectCriticalCutFreeEventMass R q
        {eta | FKRectPrimalStableCrossingWitnessCore R (insert i S) eta} ≤
      (FK.freeInfiniteVolume 2
        (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
        (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
        (zero_lt_one.trans_le hq) :
          MeasureTheory.Measure (ConfigSpace
            (Sym2 (StatMech.Lattice.Site 2)))).real
          (FK.boxBdryConnEvent 2 (R.width - 2)) *
        fkRectCriticalCutFreeEventMass R q
          {eta | FKRectPrimalStableCrossingWitnessCore R S eta} := by
  rw [fkRectCriticalCutFree_stableWitness_eq_finiteEventMass R hq,
    fkRectCriticalCutFree_stableWitness_eq_finiteEventMass R hq]
  exact fkRectPrimalFullDistinctCrossingWitness_step R S i hi
    (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
    (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) hq



theorem fkRectPrimalFullDistinctCrossingWitness_mass_le_pow
    (R : FKRectTorus) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (S : Finset (Fin R.height)) :
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectCutGraph R) p q)
        {rho | FKRectPrimalFullDistinctCrossingWitness R S rho} ≤
      ((FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        MeasureTheory.Measure (ConfigSpace
          (Sym2 (StatMech.Lattice.Site 2)))).real
        (FK.boxBdryConnEvent 2 (R.width - 2))) ^ S.card := by
  classical
  let a := (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
    MeasureTheory.Measure (ConfigSpace
      (Sym2 (StatMech.Lattice.Site 2)))).real
    (FK.boxBdryConnEvent 2 (R.width - 2))
  have ha : 0 ≤ a := MeasureTheory.measureReal_nonneg
  change StatMech.Probability.finiteEventMass
      (FK.fkProb (fkRectCutGraph R) p q)
      {rho | FKRectPrimalFullDistinctCrossingWitness R S rho} ≤ a ^ S.card
  induction S using Finset.induction_on with
  | empty =>
      calc
        StatMech.Probability.finiteEventMass
            (FK.fkProb (fkRectCutGraph R) p q)
            {rho | FKRectPrimalFullDistinctCrossingWitness R ∅ rho} = 1 := by
              unfold StatMech.Probability.finiteEventMass
              have hevent : {rho : ConfigSpace (Sym2 R.Vertex) |
                  FKRectPrimalFullDistinctCrossingWitness R ∅ rho} = Set.univ := by
                ext rho
                simp [FKRectPrimalFullDistinctCrossingWitness]
              rw [hevent]
              simpa using FK.fkProb_sum_eq_one (fkRectCutGraph R)
                hp hp1 (zero_lt_one.trans_le hq)
        _ ≤ a ^ (∅ : Finset (Fin R.height)).card := by
          rw [Finset.card_empty, pow_zero]
  | @insert i S hi ih =>
      calc
        StatMech.Probability.finiteEventMass
            (FK.fkProb (fkRectCutGraph R) p q)
            {rho | FKRectPrimalFullDistinctCrossingWitness R (insert i S) rho} ≤
          a * StatMech.Probability.finiteEventMass
            (FK.fkProb (fkRectCutGraph R) p q)
            {rho | FKRectPrimalFullDistinctCrossingWitness R S rho} :=
              fkRectPrimalFullDistinctCrossingWitness_step
                R S i hi hp hp1 hq
        _ ≤ a * a ^ S.card := mul_le_mul_of_nonneg_left ih ha
        _ = a ^ (insert i S).card := by
          rw [Finset.card_insert_of_notMem hi, pow_succ]
          ring



def fkRectPrimalFullCrossingClusterCount
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) : Nat :=
  fkRectRawHorizontalCrossingClusterCount R (fkRectCutConfigOfFull R rho).1

theorem fkRectPrimalFullCrossingClusterCount_le_height
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) :
    fkRectPrimalFullCrossingClusterCount R rho ≤ R.height :=
  fkRectRawHorizontalCrossingClusterCount_le_height R _



theorem exists_fkRectPrimalFullDistinctCrossingWitness
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) (n : Nat)
    (hn : n ≤ fkRectPrimalFullCrossingClusterCount R rho) :
    ∃ S : Finset (Fin R.height), S.card = n ∧
      FKRectPrimalFullDistinctCrossingWitness R S rho := by
  classical
  let eta := (fkRectCutConfigOfFull R rho).1
  let available := fkRectRawHorizontalCrossingRepresentativeIndices R eta
  have hnAvailable : n ≤ available.card := by
    rw [card_fkRectRawHorizontalCrossingRepresentativeIndices]
    exact hn
  obtain ⟨S, hsub, hcard⟩ := Finset.exists_subset_card_eq hnAvailable
  refine ⟨S, hcard, ?_, ?_⟩
  · intro i hi
    have hirep := hsub hi
    obtain ⟨z, hiz⟩ :=
      fkRectRawHorizontalCrossingRepresentativeIndices_subset_sources
        R eta i hirep
    refine ⟨z, ?_⟩
    rw [← fkRectOpenGraph_cutConfigOfFull R rho]
    exact hiz
  · intro i hi j hj hij hreach
    have hirep := hsub hi
    have hjrep := hsub hj
    apply hij
    apply eq_of_representativeIndices_of_component_eq R eta hirep hjrep
    apply SimpleGraph.ConnectedComponent.sound
    rw [fkRectOpenGraph_cutConfigOfFull R rho]
    exact hreach



theorem fkRectPrimalFullCrossingTail_le_choose_mul_pow
    (R : FKRectTorus) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) (n : Nat) :
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectCutGraph R) p q)
        {rho | n < fkRectPrimalFullCrossingClusterCount R rho} ≤
      Nat.choose R.height (n + 1) *
        ((FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
          MeasureTheory.Measure (ConfigSpace
            (Sym2 (StatMech.Lattice.Site 2)))).real
          (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) := by
  simpa only [Nat.lt_iff_add_one_le] using
    StatMech.Probability.finiteEventMass_tail_le_choose_mul_pow
      (FK.fkProb (fkRectCutGraph R) p q)
      (fun rho => FK.fkProb_nonneg (fkRectCutGraph R)
        hp hp1 (zero_lt_one.trans_le hq) rho)
      (fkRectPrimalFullCrossingClusterCount R) R.height (n + 1)
      ((FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        MeasureTheory.Measure (ConfigSpace
          (Sym2 (StatMech.Lattice.Site 2)))).real
        (FK.boxBdryConnEvent 2 (R.width - 2)))
      (FKRectPrimalFullDistinctCrossingWitness R)
      (fun rho htail =>
        exists_fkRectPrimalFullDistinctCrossingWitness R rho (n + 1) htail)
      (fun S hcard => by
        simpa only [hcard] using
          fkRectPrimalFullDistinctCrossingWitness_mass_le_pow
            R hp hp1 hq S)



theorem fkRectCutGraph_primalCrossingTailEvent_eq
    (R : FKRectTorus) (n : Nat) :
    FK.ecz_closeOff (fkRectCutGraph R) ⁻¹'
        fkRectCutEdgeEvent R
          {eta | n < fkRectRawHorizontalCrossingClusterCount R
            (fkRectForceCutClosed R eta)} =
      {rho | n < fkRectPrimalFullCrossingClusterCount R rho} := by
  ext rho
  change n < fkRectRawHorizontalCrossingClusterCount R
      (fkRectForceCutClosed R (fkRectCutConfigOfFull R rho).1) ↔
    n < fkRectPrimalFullCrossingClusterCount R rho
  have hforce : fkRectForceCutClosed R (fkRectCutConfigOfFull R rho).1 =
      (fkRectCutConfigOfFull R rho).1 := (fkRectCutConfigOfFull R rho).2
  rw [hforce]
  rfl



theorem fkRectCriticalCutFree_primalCrossingTail_eq_finiteEventMass
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q) (n : Nat) :
    fkRectCriticalCutFreeEventMass R q
        {eta | n < fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R eta)} =
      StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectCutGraph R) (fkRectCriticalP q) q)
        {rho | n < fkRectPrimalFullCrossingClusterCount R rho} := by
  rw [fkRectCriticalCutFreeEventMass_eq_cutGraph R hq,
    fkRectCutGraph_primalCrossingTailEvent_eq]
  unfold StatMech.Probability.finiteEventMass
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hmem : n < fkRectPrimalFullCrossingClusterCount R rho
  · have hs : rho ∈
        {rho | n < fkRectPrimalFullCrossingClusterCount R rho} := hmem
    simp [Set.indicator, hs]
  · have hs : rho ∉
        {rho | n < fkRectPrimalFullCrossingClusterCount R rho} := hmem
    simp [Set.indicator, hs]



theorem fkRectCriticalCutFree_primalCrossingTail_le_choose_mul_pow
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q) (n : Nat) :
    fkRectCriticalCutFreeEventMass R q
        {eta | n < fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R eta)} ≤
      Nat.choose R.height (n + 1) *
        ((FK.freeInfiniteVolume 2
          (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
          (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
          (zero_lt_one.trans_le hq) :
            MeasureTheory.Measure (ConfigSpace
              (Sym2 (StatMech.Lattice.Site 2)))).real
          (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) := by
  rw [fkRectCriticalCutFree_primalCrossingTail_eq_finiteEventMass R hq n]
  exact fkRectPrimalFullCrossingTail_le_choose_mul_pow R
    (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
    (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) hq n

end


end StatMech.FrontierD

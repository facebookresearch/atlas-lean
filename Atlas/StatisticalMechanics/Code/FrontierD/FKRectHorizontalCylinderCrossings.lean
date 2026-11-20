/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectHorizontalCylinderLaw









open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section


def fkRectBottomRow (R : FKRectTorus) : Fin R.height :=
  ⟨0, R.height_pos⟩


def fkRectTopRow (R : FKRectTorus) : Fin R.height :=
  ⟨R.height - 1, Nat.sub_lt R.height_pos Nat.zero_lt_one⟩



def FKRectHorizontalCylinderCrossingComponent
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (C : (FK.openSub (fkRectHorizontalCylinderGraph R) rho).ConnectedComponent) :
    Prop :=
  (∃ x : Fin R.width,
      (FK.openSub (fkRectHorizontalCylinderGraph R) rho).connectedComponentMk
        (x, fkRectBottomRow R) = C) ∧
    ∃ y : Fin R.width,
      (FK.openSub (fkRectHorizontalCylinderGraph R) rho).connectedComponentMk
        (y, fkRectTopRow R) = C


noncomputable def fkRectHorizontalCylinderCrossingClusterCount
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) : Nat := by
  classical
  exact Fintype.card
    {C // FKRectHorizontalCylinderCrossingComponent R rho C}





def FKRectHorizontalCutPrimalCrossingComponent
    (R : FKRectTorus) (eta : R.Configuration)
    (C : (fkRectOpenGraph R eta).ConnectedComponent) : Prop :=
  (∃ x : Fin R.width,
      (fkRectOpenGraph R eta).connectedComponentMk
        (x, fkRectBottomRow R) = C) ∧
    ∃ y : Fin R.width,
      (fkRectOpenGraph R eta).connectedComponentMk
        (y, fkRectTopRow R) = C



noncomputable def fkRectHorizontalCutPrimalCrossingClusterCount
    (R : FKRectTorus) (eta : R.Configuration) : Nat := by
  classical
  exact Fintype.card
    {C // FKRectHorizontalCutPrimalCrossingComponent R eta C}



theorem fkRectHorizontalCylinderCrossingClusterCount_eq_horizontalCut
    (R : FKRectTorus) (eta : FKRectHorizontalCutClosedConfig R) :
    fkRectHorizontalCylinderCrossingClusterCount R
        (fkRectHorizontalCutClosedEdgeConfigEquiv R eta).1 =
      fkRectHorizontalCutPrimalCrossingClusterCount R eta.1 := by
  classical
  let G := FK.openSub (fkRectHorizontalCylinderGraph R)
    (fkRectHorizontalCutClosedEdgeConfigEquiv R eta).1
  let H := fkRectOpenGraph R eta.1
  have hGH : G = H := fkRectHorizontalCylinder_openSub_eq R eta
  have hrel : ∀ {x y : R.Vertex}, H.Adj x y ↔ G.Adj x y := by
    intro x y
    rw [hGH]
  let phi : G ≃g H := ⟨Equiv.refl R.Vertex, hrel⟩
  let e : G.ConnectedComponent ≃ H.ConnectedComponent :=
    phi.connectedComponentEquiv
  apply Fintype.card_congr
  refine Equiv.subtypeEquiv e ?_
  intro C
  change FKRectHorizontalCylinderCrossingComponent R
      (fkRectHorizontalCutClosedEdgeConfigEquiv R eta).1 C ↔
    FKRectHorizontalCutPrimalCrossingComponent R eta.1 (e C)
  unfold FKRectHorizontalCylinderCrossingComponent
    FKRectHorizontalCutPrimalCrossingComponent
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


theorem fkRectHorizontalCylinderCrossingClusterCount_force_eq
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectHorizontalCylinderCrossingClusterCount R
        (fkRectHorizontalCutClosedEdgeConfigEquiv R
          ⟨fkRectForceHorizontalCutClosed R omega,
            fkRectHorizontalCutClosedConfiguration_force R omega⟩).1 =
      fkRectHorizontalCutPrimalCrossingClusterCount R
        (fkRectForceHorizontalCutClosed R omega) :=
  fkRectHorizontalCylinderCrossingClusterCount_eq_horizontalCut R _



theorem fkRectHorizontalCylinderCrossingTail_iff_horizontalCut
    (R : FKRectTorus) (eta : FKRectHorizontalCutClosedConfig R) (n : Nat) :
    n ≤ fkRectHorizontalCylinderCrossingClusterCount R
        (fkRectHorizontalCutClosedEdgeConfigEquiv R eta).1 ↔
      n ≤ fkRectHorizontalCutPrimalCrossingClusterCount R eta.1 := by
  rw [fkRectHorizontalCylinderCrossingClusterCount_eq_horizontalCut]


def FKRectHorizontalCylinderCrossingSource
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (x : Fin R.width) : Prop :=
  ∃ y : Fin R.width,
    (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Reachable
      (x, fkRectBottomRow R) (y, fkRectTopRow R)


noncomputable def fkRectHorizontalCylinderCrossingRepresentative
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (C : {C :
      (FK.openSub (fkRectHorizontalCylinderGraph R) rho).ConnectedComponent //
        FKRectHorizontalCylinderCrossingComponent R rho C}) : Fin R.width :=
  Classical.choose C.2.1

theorem fkRectHorizontalCylinderCrossingRepresentative_component
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (C : {C :
      (FK.openSub (fkRectHorizontalCylinderGraph R) rho).ConnectedComponent //
        FKRectHorizontalCylinderCrossingComponent R rho C}) :
    (FK.openSub (fkRectHorizontalCylinderGraph R) rho).connectedComponentMk
        (fkRectHorizontalCylinderCrossingRepresentative R rho C,
          fkRectBottomRow R) = C.1 :=
  Classical.choose_spec C.2.1

theorem fkRectHorizontalCylinderCrossingRepresentative_source
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (C : {C :
      (FK.openSub (fkRectHorizontalCylinderGraph R) rho).ConnectedComponent //
        FKRectHorizontalCylinderCrossingComponent R rho C}) :
    FKRectHorizontalCylinderCrossingSource R rho
      (fkRectHorizontalCylinderCrossingRepresentative R rho C) := by
  rcases C.2.2 with ⟨y, hy⟩
  refine ⟨y, SimpleGraph.ConnectedComponent.exact ?_⟩
  exact (fkRectHorizontalCylinderCrossingRepresentative_component
    R rho C).trans hy.symm

theorem fkRectHorizontalCylinderCrossingRepresentative_injective
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) :
    Function.Injective
      (fkRectHorizontalCylinderCrossingRepresentative R rho) := by
  intro C D hCD
  apply Subtype.ext
  exact (fkRectHorizontalCylinderCrossingRepresentative_component
    R rho C).symm.trans
      ((congrArg
        (fun x =>
          (FK.openSub (fkRectHorizontalCylinderGraph R) rho).connectedComponentMk
            (x, fkRectBottomRow R)) hCD).trans
        (fkRectHorizontalCylinderCrossingRepresentative_component R rho D))


noncomputable def fkRectHorizontalCylinderCrossingRepresentativeIndices
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) :
    Finset (Fin R.width) := by
  classical
  exact Finset.univ.image
    (fkRectHorizontalCylinderCrossingRepresentative R rho)

theorem card_fkRectHorizontalCylinderCrossingRepresentativeIndices
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) :
    (fkRectHorizontalCylinderCrossingRepresentativeIndices R rho).card =
      fkRectHorizontalCylinderCrossingClusterCount R rho := by
  classical
  unfold fkRectHorizontalCylinderCrossingRepresentativeIndices
  rw [Finset.card_image_of_injective]
  · rfl
  · exact fkRectHorizontalCylinderCrossingRepresentative_injective R rho

theorem fkRectHorizontalCylinderCrossingRepresentativeIndices_subset_sources
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) :
    ∀ x ∈ fkRectHorizontalCylinderCrossingRepresentativeIndices R rho,
      FKRectHorizontalCylinderCrossingSource R rho x := by
  classical
  intro x hx
  unfold fkRectHorizontalCylinderCrossingRepresentativeIndices at hx
  rw [Finset.mem_image] at hx
  rcases hx with ⟨C, _, rfl⟩
  exact fkRectHorizontalCylinderCrossingRepresentative_source R rho C

theorem eq_of_horizontalCylinder_representatives_of_component_eq
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    {x y : Fin R.width}
    (hx : x ∈ fkRectHorizontalCylinderCrossingRepresentativeIndices R rho)
    (hy : y ∈ fkRectHorizontalCylinderCrossingRepresentativeIndices R rho)
    (hcomponent :
      (FK.openSub (fkRectHorizontalCylinderGraph R) rho).connectedComponentMk
          (x, fkRectBottomRow R) =
        (FK.openSub (fkRectHorizontalCylinderGraph R) rho).connectedComponentMk
          (y, fkRectBottomRow R)) :
    x = y := by
  classical
  unfold fkRectHorizontalCylinderCrossingRepresentativeIndices at hx hy
  rw [Finset.mem_image] at hx hy
  rcases hx with ⟨C, _, rfl⟩
  rcases hy with ⟨D, _, rfl⟩
  have hCD : C = D := by
    apply Subtype.ext
    exact (fkRectHorizontalCylinderCrossingRepresentative_component
      R rho C).symm.trans
        (hcomponent.trans
          (fkRectHorizontalCylinderCrossingRepresentative_component
            R rho D))
  exact congrArg
    (fkRectHorizontalCylinderCrossingRepresentative R rho) hCD



noncomputable def fkRectHorizontalCylinderCrossingTarget
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (x : Fin R.width) : Fin R.width := by
  classical
  exact if h : FKRectHorizontalCylinderCrossingSource R rho x then
      Classical.choose h
    else fkRectLeftColumn R

theorem fkRectHorizontalCylinderCrossingTarget_reachable
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    {x : Fin R.width}
    (hx : FKRectHorizontalCylinderCrossingSource R rho x) :
    (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Reachable
      (x, fkRectBottomRow R)
      (fkRectHorizontalCylinderCrossingTarget R rho x,
        fkRectTopRow R) := by
  classical
  rw [fkRectHorizontalCylinderCrossingTarget, dif_pos hx]
  exact Classical.choose_spec hx



def FKRectHorizontalCylinderDistinctPairedWitness
    (R : FKRectTorus) (pair : Fin R.width -> Fin R.width)
    (S : Finset (Fin R.width))
    (rho : ConfigSpace (Sym2 R.Vertex)) : Prop :=
  (∀ x ∈ S,
    (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Reachable
      (x, fkRectBottomRow R) (pair x, fkRectTopRow R)) ∧
  (∀ x ∈ S, ∀ y ∈ S, x ≠ y ->
    ¬ (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Reachable
      (x, fkRectBottomRow R) (y, fkRectBottomRow R))



theorem exists_fkRectHorizontalCylinderDistinctPairedWitness
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) (n : Nat)
    (hn : n <= fkRectHorizontalCylinderCrossingClusterCount R rho) :
    ∃ S : Finset (Fin R.width), S.card = n ∧
      FKRectHorizontalCylinderDistinctPairedWitness R
        (fkRectHorizontalCylinderCrossingTarget R rho) S rho := by
  classical
  let available :=
    fkRectHorizontalCylinderCrossingRepresentativeIndices R rho
  have hnAvailable : n <= available.card := by
    rw [card_fkRectHorizontalCylinderCrossingRepresentativeIndices]
    exact hn
  obtain ⟨S, hsub, hcard⟩ :=
    Finset.exists_subset_card_eq hnAvailable
  refine ⟨S, hcard, ?_, ?_⟩
  · intro x hx
    exact fkRectHorizontalCylinderCrossingTarget_reachable R rho
      (fkRectHorizontalCylinderCrossingRepresentativeIndices_subset_sources
        R rho x (hsub hx))
  · intro x hx y hy hxy hreach
    apply hxy
    apply eq_of_horizontalCylinder_representatives_of_component_eq
      R rho (hsub hx) (hsub hy)
    exact SimpleGraph.ConnectedComponent.sound hreach




theorem fkRectHorizontalCylinderCrossingTail_le_choose_mul_pairCount_mul
    (R : FKRectTorus)
    (mu : ConfigSpace (Sym2 R.Vertex) -> Real)
    (hmu : ∀ rho, 0 <= mu rho) (n : Nat) (a : Real)
    (hmass : ∀ S : Finset (Fin R.width), S.card = n ->
      ∀ pair : Fin R.width -> Fin R.width,
        StatMech.Probability.finiteEventMass mu
          {rho | FKRectHorizontalCylinderDistinctPairedWitness
            R pair S rho} <= a) :
    StatMech.Probability.finiteEventMass mu
        {rho | n <= fkRectHorizontalCylinderCrossingClusterCount R rho} <=
      Nat.choose R.width n * R.width ^ R.width * a := by
  classical
  let subsets : Finset (Finset (Fin R.width)) :=
    (Finset.univ : Finset (Fin R.width)).powersetCard n
  let Pair := Fin R.width -> Fin R.width
  have hpoint (rho : ConfigSpace (Sym2 R.Vertex)) :
      (if n <= fkRectHorizontalCylinderCrossingClusterCount R rho then
          mu rho else 0) <=
        subsets.sum (fun S =>
          (Finset.univ : Finset Pair).sum (fun pair =>
            if FKRectHorizontalCylinderDistinctPairedWitness
                R pair S rho then mu rho else 0)) := by
    by_cases htail : n <=
        fkRectHorizontalCylinderCrossingClusterCount R rho
    · rw [if_pos htail]
      obtain ⟨S, hcard, hW⟩ :=
        exists_fkRectHorizontalCylinderDistinctPairedWitness
          R rho n htail
      let pair := fkRectHorizontalCylinderCrossingTarget R rho
      have hS : S ∈ subsets := by
        simp [subsets, hcard]
      have hpair : pair ∈ (Finset.univ : Finset Pair) :=
        Finset.mem_univ pair
      have hinner : mu rho <=
          (Finset.univ : Finset Pair).sum (fun target =>
            if FKRectHorizontalCylinderDistinctPairedWitness
                R target S rho then mu rho else 0) := by
        have hsingle := Finset.single_le_sum
          (s := (Finset.univ : Finset Pair))
          (f := fun target =>
            if FKRectHorizontalCylinderDistinctPairedWitness
                R target S rho then mu rho else 0)
          (fun target _ => by
            by_cases htarget :
                FKRectHorizontalCylinderDistinctPairedWitness
                  R target S rho <;>
              simp [htarget, hmu rho]) hpair
        simpa [pair, hW] using hsingle
      exact hinner.trans (Finset.single_le_sum
        (s := subsets)
        (f := fun T =>
          (Finset.univ : Finset Pair).sum (fun target =>
            if FKRectHorizontalCylinderDistinctPairedWitness
                R target T rho then mu rho else 0))
        (fun T _ => Finset.sum_nonneg fun target _ => by
          by_cases htarget :
              FKRectHorizontalCylinderDistinctPairedWitness
                R target T rho <;>
            simp [htarget, hmu rho]) hS)
    · rw [if_neg htail]
      exact Finset.sum_nonneg fun S _ =>
        Finset.sum_nonneg fun pair _ => by
          by_cases hpair :
              FKRectHorizontalCylinderDistinctPairedWitness
                R pair S rho <;>
            simp [hpair, hmu rho]
  calc
    StatMech.Probability.finiteEventMass mu
        {rho | n <= fkRectHorizontalCylinderCrossingClusterCount R rho} =
      ∑ rho, if n <=
          fkRectHorizontalCylinderCrossingClusterCount R rho then
        mu rho else 0 := by
          unfold StatMech.Probability.finiteEventMass
          apply Finset.sum_congr rfl
          intro rho _
          simp
    _ <= ∑ rho, subsets.sum (fun S =>
        (Finset.univ : Finset Pair).sum (fun pair =>
          if FKRectHorizontalCylinderDistinctPairedWitness
              R pair S rho then mu rho else 0)) :=
      Finset.sum_le_sum fun rho _ => hpoint rho
    _ = subsets.sum (fun S =>
        (Finset.univ : Finset Pair).sum (fun pair =>
          StatMech.Probability.finiteEventMass mu
            {rho | FKRectHorizontalCylinderDistinctPairedWitness
              R pair S rho})) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro pair _
      unfold StatMech.Probability.finiteEventMass
      apply Finset.sum_congr rfl
      intro rho _
      rfl
    _ <= subsets.sum (fun _ =>
        (Finset.univ : Finset Pair).sum (fun _ => a)) := by
      apply Finset.sum_le_sum
      intro S hS
      have hcard : S.card = n := by
        simpa [subsets] using hS
      exact Finset.sum_le_sum fun pair _ => hmass S hcard pair
    _ = Nat.choose R.width n * R.width ^ R.width * a := by
      simp [subsets, Pair, Finset.card_powersetCard]
      ring

theorem fkRectHorizontalCutClosedConfiguration_force_eq_self
    (R : FKRectTorus) (eta : R.Configuration)
    (hclosed : FKRectHorizontalCutClosedConfiguration R eta) :
    fkRectForceHorizontalCutClosed R eta = eta := by
  funext a
  by_cases ha : a ∈ fkRectHorizontalCutEdges R
  · simp [fkRectForceHorizontalCutClosed, fkRectForceEdgesClosed,
      ha, hclosed a ha]
  · simp [fkRectForceHorizontalCutClosed, fkRectForceEdgesClosed, ha]


theorem openSub_ecz_closeOff_horizontalCylinder
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) :
    FK.openSub (fkRectHorizontalCylinderGraph R)
        (FK.ecz_closeOff (fkRectHorizontalCylinderGraph R) rho).1 =
      FK.openSub (fkRectHorizontalCylinderGraph R) rho := by
  apply SimpleGraph.ext
  ext x y
  simp only [FK.openSub_adj]
  constructor
  · rintro ⟨hxy, hopen⟩
    exact ⟨hxy, by
      have hedge : s(x, y) ∈
          (fkRectHorizontalCylinderGraph R).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset]
        exact hxy
      simpa using (FK.ecz_closeOff_apply_edge
        (fkRectHorizontalCylinderGraph R) rho hedge).symm.trans hopen⟩
  · rintro ⟨hxy, hopen⟩
    refine ⟨hxy, ?_⟩
    have hedge : s(x, y) ∈
        (fkRectHorizontalCylinderGraph R).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset]
      exact hxy
    simpa using (FK.ecz_closeOff_apply_edge
      (fkRectHorizontalCylinderGraph R) rho hedge).trans hopen

theorem FKRectHorizontalCylinderDistinctPairedWitness.congr_openSub
    (R : FKRectTorus) (pair : Fin R.width -> Fin R.width)
    (S : Finset (Fin R.width))
    {rho sigma : ConfigSpace (Sym2 R.Vertex)}
    (hgraph : FK.openSub (fkRectHorizontalCylinderGraph R) rho =
      FK.openSub (fkRectHorizontalCylinderGraph R) sigma) :
    FKRectHorizontalCylinderDistinctPairedWitness R pair S rho ↔
      FKRectHorizontalCylinderDistinctPairedWitness R pair S sigma := by
  unfold FKRectHorizontalCylinderDistinctPairedWitness
  rw [hgraph]


def FKRectHorizontalCylinderStablePairedWitnessCore
    (R : FKRectTorus) (pair : Fin R.width -> Fin R.width)
    (S : Finset (Fin R.width)) (eta : R.Configuration) : Prop :=
  FKRectHorizontalCylinderDistinctPairedWitness R pair S
    (fkRectFullGraphConfiguration R
      (fkRectForceHorizontalCutClosed R eta))

theorem fkRectHorizontalCylinderStablePairedWitness_edgeEvent_eq
    (R : FKRectTorus) (pair : Fin R.width -> Fin R.width)
    (S : Finset (Fin R.width)) :
    FK.ecz_closeOff (fkRectHorizontalCylinderGraph R) ⁻¹'
        fkRectHorizontalCylinderEdgeEvent R
          {eta | FKRectHorizontalCylinderStablePairedWitnessCore
            R pair S eta} =
      {rho | FKRectHorizontalCylinderDistinctPairedWitness
        R pair S rho} := by
  ext rho
  let sigma := FK.ecz_closeOff (fkRectHorizontalCylinderGraph R) rho
  let eta :=
    (fkRectHorizontalCutClosedEdgeConfigEquiv R).symm sigma
  change FKRectHorizontalCylinderStablePairedWitnessCore
      R pair S eta.1 ↔ _
  have hclosed : fkRectForceHorizontalCutClosed R eta.1 = eta.1 :=
    fkRectHorizontalCutClosedConfiguration_force_eq_self
      R eta.1 eta.2
  unfold FKRectHorizontalCylinderStablePairedWitnessCore
  rw [hclosed]
  have hequiv :
      fkRectHorizontalCutClosedEdgeConfigEquiv R eta = sigma := by
    exact (fkRectHorizontalCutClosedEdgeConfigEquiv R).apply_symm_apply sigma
  have hval : fkRectFullGraphConfiguration R eta.1 = sigma.1 := by
    rw [← fkRectHorizontalCutClosedEdgeConfigEquiv_apply]
    exact congrArg Subtype.val hequiv
  rw [hval]
  apply FKRectHorizontalCylinderDistinctPairedWitness.congr_openSub
  exact openSub_ecz_closeOff_horizontalCylinder R rho



theorem fkRectCriticalHorizontalCut_stablePairedWitness_eq_finiteEventMass
    (R : FKRectTorus) (pair : Fin R.width -> Fin R.width)
    {q : Real} (hq : 1 <= q) (S : Finset (Fin R.width)) :
    fkRectCriticalHorizontalCutEventMass R q
        {eta | FKRectHorizontalCylinderStablePairedWitnessCore
          R pair S eta} =
      StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectHorizontalCylinderGraph R)
          (fkRectCriticalP q) q)
        {rho | FKRectHorizontalCylinderDistinctPairedWitness
          R pair S rho} := by
  rw [fkRectCriticalHorizontalCutEventMass_eq_cylinderGraph R hq,
    fkRectHorizontalCylinderStablePairedWitness_edgeEvent_eq]
  unfold StatMech.Probability.finiteEventMass
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hmem :
      FKRectHorizontalCylinderDistinctPairedWitness R pair S rho <;>
    simp [Set.indicator, hmem]

end

end StatMech.FrontierD

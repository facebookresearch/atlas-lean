/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexFKFiniteWiredWeights









open Finset SimpleGraph
open scoped BigOperators

namespace StatMech.FK

open StatMech.Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
  (boundary : V -> Prop) [DecidablePred boundary]

def activeGraphEdgeIncl (hGH : G <= H) : G.edgeSet ↪ H.edgeSet where
  toFun e := ⟨e.1, SimpleGraph.edgeSet_mono hGH e.2⟩
  inj' _ _ h := Subtype.ext (congrArg (fun e : H.edgeSet => e.1) h)


def activeGraphRestrict (hGH : G <= H)
    (eta : ConfigSpace H.edgeSet) : ConfigSpace G.edgeSet :=
  fun e => eta (activeGraphEdgeIncl G H hGH e)


abbrev AddedEdge := {e : H.edgeSet // e.1 ∉ G.edgeSet}

def activeGraphInnerEdgeEquiv (hGH : G <= H) :
    G.edgeSet ≃ {e : H.edgeSet // e.1 ∈ G.edgeSet} where
  toFun e := ⟨activeGraphEdgeIncl G H hGH e, e.2⟩
  invFun e := ⟨e.1.1, e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl


def activeGraphEdgeSplitEquiv (hGH : G <= H) :
    H.edgeSet ≃ G.edgeSet ⊕ AddedEdge G H :=
  (((activeGraphInnerEdgeEquiv G H hGH).sumCongr
      (Equiv.refl (AddedEdge G H))).trans
    (Equiv.sumCompl (fun e : H.edgeSet => e.1 ∈ G.edgeSet))).symm


def activeGraphConfigSplitEquiv (hGH : G <= H) :
    ConfigSpace H.edgeSet ≃
      ConfigSpace G.edgeSet × ConfigSpace (AddedEdge G H) where
  toFun eta :=
    (fun e => eta ((activeGraphEdgeSplitEquiv G H hGH).symm (Sum.inl e)),
      fun e => eta ((activeGraphEdgeSplitEquiv G H hGH).symm (Sum.inr e)))
  invFun pair e :=
    match activeGraphEdgeSplitEquiv G H hGH e with
    | Sum.inl a => pair.1 a
    | Sum.inr a => pair.2 a
  left_inv eta := by
    funext e
    rcases h : activeGraphEdgeSplitEquiv G H hGH e with a | a
    · simp only [h]
      rw [show (activeGraphEdgeSplitEquiv G H hGH).symm (Sum.inl a) = e by
        rw [← h]; exact (activeGraphEdgeSplitEquiv G H hGH).symm_apply_apply e]
    · simp only [h]
      rw [show (activeGraphEdgeSplitEquiv G H hGH).symm (Sum.inr a) = e by
        rw [← h]; exact (activeGraphEdgeSplitEquiv G H hGH).symm_apply_apply e]
  right_inv pair := by
    apply Prod.ext <;> funext e
    · simp [activeGraphEdgeSplitEquiv, activeGraphInnerEdgeEquiv,
        activeGraphEdgeIncl]
    · simp [activeGraphEdgeSplitEquiv, activeGraphInnerEdgeEquiv,
        activeGraphEdgeIncl]

@[simp] theorem activeGraphRestrict_configSplit_symm
    (hGH : G <= H) (rho : ConfigSpace G.edgeSet)
    (xi : ConfigSpace (AddedEdge G H)) :
    activeGraphRestrict G H hGH
        ((activeGraphConfigSplitEquiv G H hGH).symm (rho, xi)) = rho := by
  funext e
  simp [activeGraphRestrict, activeGraphConfigSplitEquiv,
    activeGraphEdgeSplitEquiv, activeGraphInnerEdgeEquiv,
    activeGraphEdgeIncl]

theorem openSub_extendActive_restrictActive_eq
    (omega : ConfigSpace (Sym2 V)) :
    openSub G (extendActive G (restrictActive G omega)) = openSub G omega := by
  apply ecz_openSub_eq_of_edges G
  intro e he
  have heSet : e ∈ G.edgeSet := by
    rwa [← SimpleGraph.mem_edgeFinset]
  simpa [restrictActive] using
    (extendActive_apply G (restrictActive G omega) ⟨e, heSet⟩)



theorem wiredGraph_eq_of_le_sup_boundaryClique
    (hGH : G <= H)
    (habsorb : H <= G ⊔ boundaryCliqueGraph boundary)
    (eta : ConfigSpace H.edgeSet) :
    wiredGraph H boundary (extendActive H eta) =
      wiredGraph G boundary
        (extendActive G (activeGraphRestrict G H hGH eta)) := by
  ext x y
  rw [wiredGraph_adj, wiredGraph_adj]
  constructor
  · rintro (⟨hH, hopen⟩ | hb)
    · by_cases hG : G.Adj x y
      · left
        refine ⟨hG, ?_⟩
        have hGedge : s(x, y) ∈ G.edgeSet := by
          rwa [SimpleGraph.mem_edgeSet]
        have hHedge : s(x, y) ∈ H.edgeSet := by
          rwa [SimpleGraph.mem_edgeSet]
        simpa [extendActive, activeGraphRestrict, activeGraphEdgeIncl,
          hGedge, hHedge] using hopen
      · right
        rcases habsorb hH with hG' | hb
        · exact (hG hG').elim
        · rw [boundaryCliqueGraph_adj] at hb
          exact hb
    · exact Or.inr hb
  · rintro (⟨hG, hopen⟩ | hb)
    · left
      refine ⟨hGH hG, ?_⟩
      have hGedge : s(x, y) ∈ G.edgeSet := by
        rwa [SimpleGraph.mem_edgeSet]
      have hHedge : s(x, y) ∈ H.edgeSet := by
        rw [SimpleGraph.mem_edgeSet]
        exact hGH hG
      simpa [extendActive, activeGraphRestrict, activeGraphEdgeIncl,
        hGedge, hHedge] using hopen
    · exact Or.inr hb

theorem numClustersWired_eq_of_le_sup_boundaryClique
    (hGH : G <= H)
    (habsorb : H <= G ⊔ boundaryCliqueGraph boundary)
    (eta : ConfigSpace H.edgeSet) :
    numClustersWired H boundary (extendActive H eta) =
      numClustersWired G boundary
        (extendActive G (activeGraphRestrict G H hGH eta)) := by
  unfold numClustersWired
  rw [wiredGraph_eq_of_le_sup_boundaryClique G H boundary hGH habsorb eta]



theorem edgeProductW_configSplit_symm
    (hGH : G <= H) (p : Real)
    (rho : ConfigSpace G.edgeSet) (xi : ConfigSpace (AddedEdge G H)) :
    edgeProductW H (fun _ => p)
        (extendActive H ((activeGraphConfigSplitEquiv G H hGH).symm (rho, xi))) =
      edgeProductW G (fun _ => p) (extendActive G rho) *
        ∏ e : AddedEdge G H, if xi e then p else 1 - p := by
  rw [PeriodicPlanar.edgeProductW_extendActive_eq_activeProduct,
    PeriodicPlanar.edgeProductW_extendActive_eq_activeProduct]
  calc
    (∏ e : H.edgeSet,
        if (activeGraphConfigSplitEquiv G H hGH).symm (rho, xi) e
          then p else 1 - p) =
      ∏ a : G.edgeSet ⊕ AddedEdge G H,
        if (activeGraphConfigSplitEquiv G H hGH).symm (rho, xi)
            ((activeGraphEdgeSplitEquiv G H hGH).symm a)
          then p else 1 - p := by
        apply Fintype.prod_equiv (activeGraphEdgeSplitEquiv G H hGH)
        intro e
        simp
    _ = _ := by
      rw [Fintype.prod_sum_type]
      congr 1
      · apply Fintype.prod_congr
        intro e
        simp [activeGraphConfigSplitEquiv]
      · apply Fintype.prod_congr
        intro e
        simp [activeGraphConfigSplitEquiv]

theorem addedBernoulliWeight_sum (p : Real) :
    (∑ xi : ConfigSpace (AddedEdge G H),
      (∏ e, if xi e then p else 1 - p)) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : AddedEdge G H) (b : Bool) =>
    if b then p else 1 - p)]
  simp



theorem activeBCWeight_configSplit_symm
    (hGH : G <= H)
    (habsorb : H <= G ⊔ boundaryCliqueGraph boundary)
    (p q : Real) (rho : ConfigSpace G.edgeSet)
    (xi : ConfigSpace (AddedEdge G H)) :
    activeBCWeight H (boundaryCliqueGraph boundary) (fun _ => p) q
        ((activeGraphConfigSplitEquiv G H hGH).symm (rho, xi)) =
      (∏ e, if xi e then p else 1 - p) *
        activeBCWeight G (boundaryCliqueGraph boundary) (fun _ => p) q rho := by
  unfold activeBCWeight
  rw [edgeProductW_configSplit_symm G H hGH]
  rw [numClustersBC_boundaryClique, numClustersBC_boundaryClique]
  rw [numClustersWired_eq_of_le_sup_boundaryClique G H boundary hGH habsorb]
  rw [activeGraphRestrict_configSplit_symm]
  ring



theorem activeBCZ_eq_of_le_sup_boundaryClique
    (hGH : G <= H)
    (habsorb : H <= G ⊔ boundaryCliqueGraph boundary)
    (p q : Real) :
    activeBCZ H (boundaryCliqueGraph boundary) (fun _ => p) q =
      activeBCZ G (boundaryCliqueGraph boundary) (fun _ => p) q := by
  unfold activeBCZ
  rw [← Equiv.sum_comp (activeGraphConfigSplitEquiv G H hGH).symm,
    Fintype.sum_prod_type]
  simp_rw [activeBCWeight_configSplit_symm G H boundary hGH habsorb]
  calc
    (∑ rho : ConfigSpace G.edgeSet,
      ∑ xi : ConfigSpace (AddedEdge G H),
        (∏ e : AddedEdge G H, if xi e then p else 1 - p) *
          activeBCWeight G (boundaryCliqueGraph boundary) (fun _ => p) q rho) =
      ∑ rho : ConfigSpace G.edgeSet,
        (∑ xi : ConfigSpace (AddedEdge G H),
          ∏ e : AddedEdge G H, if xi e then p else 1 - p) *
          activeBCWeight G (boundaryCliqueGraph boundary) (fun _ => p) q rho := by
        apply Finset.sum_congr rfl
        intro rho _
        rw [Finset.sum_mul]
    _ = _ := by rw [addedBernoulliWeight_sum G H]; simp



theorem activeBCNumer_eq_of_le_sup_boundaryClique
    (hGH : G <= H)
    (habsorb : H <= G ⊔ boundaryCliqueGraph boundary)
    (p q : Real) (f : ConfigSpace G.edgeSet -> Real) :
    activeBCNumer H (boundaryCliqueGraph boundary) (fun _ => p) q
        (fun eta => f (activeGraphRestrict G H hGH eta)) =
      activeBCNumer G (boundaryCliqueGraph boundary) (fun _ => p) q f := by
  unfold activeBCNumer
  rw [← Equiv.sum_comp (activeGraphConfigSplitEquiv G H hGH).symm,
    Fintype.sum_prod_type]
  simp_rw [activeGraphRestrict_configSplit_symm,
    activeBCWeight_configSplit_symm G H boundary hGH habsorb]
  calc
    (∑ rho : ConfigSpace G.edgeSet,
      ∑ xi : ConfigSpace (AddedEdge G H), f rho *
        ((∏ e : AddedEdge G H, if xi e then p else 1 - p) *
          activeBCWeight G (boundaryCliqueGraph boundary) (fun _ => p) q rho)) =
      ∑ rho : ConfigSpace G.edgeSet,
        (∑ xi : ConfigSpace (AddedEdge G H),
          ∏ e : AddedEdge G H, if xi e then p else 1 - p) *
        (f rho * activeBCWeight G (boundaryCliqueGraph boundary)
          (fun _ => p) q rho) := by
        apply Finset.sum_congr rfl
        intro rho _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro xi _
        ring
    _ = _ := by rw [addedBernoulliWeight_sum G H]; simp




theorem activeBCMean_eq_of_le_sup_boundaryClique
    (hGH : G <= H)
    (habsorb : H <= G ⊔ boundaryCliqueGraph boundary)
    (p q : Real) (f : ConfigSpace G.edgeSet -> Real) :
    activeBCMean H (boundaryCliqueGraph boundary) (fun _ => p) q
        (fun eta => f (activeGraphRestrict G H hGH eta)) =
      activeBCMean G (boundaryCliqueGraph boundary) (fun _ => p) q f := by
  rw [activeBCMean_eq_div, activeBCMean_eq_div,
    activeBCNumer_eq_of_le_sup_boundaryClique G H boundary hGH habsorb,
    activeBCZ_eq_of_le_sup_boundaryClique G H boundary hGH habsorb]



theorem exists_boundary_reachable_of_sup_boundaryClique
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {root : V} (hroot : ¬ boundary root) {y : V} (hy : boundary y)
    (hreach : (A ⊔ boundaryCliqueGraph boundary).Reachable root y) :
    ∃ z : V, boundary z ∧ A.Reachable root z := by
  obtain ⟨walk⟩ := hreach
  induction walk with
  | nil => exact (hroot hy).elim
  | @cons x y z hxy walk ih =>
      rcases hxy with hA | hclique
      · by_cases hy' : boundary y
        · exact ⟨y, hy', hA.reachable⟩
        · obtain ⟨w, hw, hreach⟩ := ih hy' hy
          exact ⟨w, hw, hA.reachable.trans hreach⟩
      · rw [boundaryCliqueGraph_adj] at hclique
        exact (hroot hclique.2.1).elim



theorem boundaryReachable_iff_of_le_sup_boundaryClique
    (hGH : G <= H)
    (habsorb : H <= G ⊔ boundaryCliqueGraph boundary)
    {root : V} (hroot : ¬ boundary root)
    (eta : ConfigSpace H.edgeSet) :
    (∃ y : V, boundary y ∧
        (openSub H (extendActive H eta)).Reachable root y) ↔
      ∃ y : V, boundary y ∧
        (openSub G (extendActive G
          (activeGraphRestrict G H hGH eta))).Reachable root y := by
  rw [openSub_eq_openGraph, openSub_eq_openGraph]
  constructor
  · rintro ⟨y, hy, hreach⟩
    have hwired : (wiredGraph H boundary (extendActive H eta)).Reachable root y :=
      hreach.mono le_sup_left
    rw [wiredGraph_eq_of_le_sup_boundaryClique G H boundary
      hGH habsorb eta] at hwired
    exact exists_boundary_reachable_of_sup_boundaryClique
      (A := openGraph G
        (extendActive G (activeGraphRestrict G H hGH eta)))
      (boundary := boundary) hroot hy (by simpa [wiredGraph] using hwired)
  · rintro ⟨y, hy, hreach⟩
    refine ⟨y, hy, hreach.mono ?_⟩
    intro x z hxz
    rw [openGraph_adj] at hxz ⊢
    refine ⟨hGH hxz.1, ?_⟩
    have hGedge : s(x, z) ∈ G.edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      exact hxz.1
    have hHedge : s(x, z) ∈ H.edgeSet := by
      exact SimpleGraph.edgeSet_mono hGH hGedge
    simpa [extendActive, activeGraphRestrict, activeGraphEdgeIncl,
      hGedge, hHedge] using hxz.2

section NestedBoundary

variable {Vin Vout : Type*} [DecidableEq Vin] [DecidableEq Vout]
  (Gin : SimpleGraph Vin) (Gout : SimpleGraph Vout)
  (incl : Vin → Vout)
  (bdryIn : Vin → Prop) (bdryOut : Vout → Prop)


def finiteRootBoundaryEvent {W : Type*} (K : SimpleGraph W)
    (bdry : W → Prop) (root : W) : Set (ConfigSpace (Sym2 W)) :=
  {omega | ∃ y, bdry y ∧ (openSub K omega).Reachable root y}

theorem finiteRootBoundaryEvent_isIncreasing {W : Type*}
    (K : SimpleGraph W) (bdry : W → Prop) (root : W) :
    IsIncreasing (finiteRootBoundaryEvent K bdry root) := by
  intro omega eta home
  rintro ⟨y, hy, hreach⟩
  refine ⟨y, hy, hreach.mono ?_⟩
  intro x z hxz
  rw [openSub_adj] at hxz ⊢
  refine ⟨hxz.1, Bool.eq_true_of_true_le ?_⟩
  simpa [hxz.2] using home s(x, z)

noncomputable def finiteWiredEventMass {W : Type*} [Fintype W]
    [DecidableEq W] (K : SimpleGraph W) [DecidableRel K.Adj]
    (bdry : W → Prop) [DecidablePred bdry]
    (p q : Real) (A : Set (ConfigSpace (Sym2 W))) : Real :=
  ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
    wiredFkProb K bdry p q omega

theorem finiteWiredEventMass_mono {W : Type*} [Fintype W]
    [DecidableEq W] (K : SimpleGraph W) [DecidableRel K.Adj]
    (bdry : W → Prop) [DecidablePred bdry]
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    {A B : Set (ConfigSpace (Sym2 W))} (hAB : A ⊆ B) :
    finiteWiredEventMass K bdry p q A ≤
      finiteWiredEventMass K bdry p q B := by
  unfold finiteWiredEventMass
  apply Finset.sum_le_sum
  intro omega _
  apply mul_le_mul_of_nonneg_right _
    (wiredFkProb_nonneg K bdry hp hp1 hq omega)
  by_cases hA : omega ∈ A
  · simp [Set.indicator_of_mem hA, Set.indicator_of_mem (hAB hA)]
  · by_cases hB : omega ∈ B <;> simp [hA, hB]



theorem ocd_boundaryReach_of_outerBoundaryReach
    (hadj : ocd_AdjMatch Gin Gout incl)
    (hmargin : ∀ x, ¬ bdryOut (incl x))
    (hcross : ∀ x c, Gout.Adj (incl x) c →
      c ∉ Set.range incl → bdryIn x)
    (rho : ConfigSpace (Sym2 Vout)) (root : Vin)
    (hreach : ∃ y, bdryOut y ∧
      (openSub Gout rho).Reachable (incl root) y) :
    ∃ z, bdryIn z ∧
      (openSub Gin (ocd_innerRestrict incl rho)).Reachable root z := by
  obtain ⟨y, hy, p⟩ := hreach
  obtain ⟨walk⟩ := p
  have go : ∀ {a y : Vout} (walk : (openSub Gout rho).Walk a y),
      ∀ x : Vin, a = incl x → bdryOut y →
        ∃ z, bdryIn z ∧
          (openSub Gin (ocd_innerRestrict incl rho)).Reachable x z := by
    intro a y walk
    induction walk with
    | nil =>
        intro x hax hy'
        exact (hmargin x (hax ▸ hy')).elim
    | @cons a b y hab walk ih =>
        intro x hax hy'
        subst a
        by_cases hx : bdryIn x
        · exact ⟨x, hx, .refl x⟩
        · by_cases hb : b ∈ Set.range incl
          · obtain ⟨w, rfl⟩ := hb
            have habIn : (openSub Gin
                (ocd_innerRestrict incl rho)).Adj x w := by
              rw [openSub_adj] at hab ⊢
              refine ⟨(hadj x w).2 hab.1, ?_⟩
              simpa [ocd_innerRestrict, ocd_innerEdge_mk] using hab.2
            obtain ⟨z, hz, hwz⟩ := ih w rfl hy'
            exact ⟨z, hz, habIn.reachable.trans hwz⟩
          · rw [openSub_adj] at hab
            exact ⟨x, hcross x b hab.1 hb, .refl x⟩
  exact go walk root rfl hy

theorem outerRootBoundaryEvent_subset_innerRestrict
    (hadj : ocd_AdjMatch Gin Gout incl)
    (hmargin : ∀ x, ¬ bdryOut (incl x))
    (hcross : ∀ x c, Gout.Adj (incl x) c →
      c ∉ Set.range incl → bdryIn x)
    (root : Vin) :
    finiteRootBoundaryEvent Gout bdryOut (incl root) ⊆
      ocd_innerRestrict incl ⁻¹'
        finiteRootBoundaryEvent Gin bdryIn root := by
  intro rho hrho
  exact ocd_boundaryReach_of_outerBoundaryReach Gin Gout incl bdryIn bdryOut
    hadj hmargin hcross rho root hrho

end NestedBoundary

end

end StatMech.FK

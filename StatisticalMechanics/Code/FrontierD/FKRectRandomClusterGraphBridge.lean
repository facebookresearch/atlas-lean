/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectConnectedInsertionCharge
import Code.FK.RandomCluster











open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section



theorem mem_fkRectTorusGraph_edgeSet_iff (R : FKRectTorus)
    (e : Sym2 R.Vertex) :
    e ∈ (fkRectTorusGraph R).edgeSet ↔
      ∃ a : R.EdgeIndex, fkRectTorusIndexedEdge R a = e := by
  obtain ⟨⟨x, y⟩, rfl⟩ := Quot.exists_rep e
  rw [SimpleGraph.mem_edgeSet]
  rfl



def fkRectEdgeToGraphEdge (R : FKRectTorus) (a : R.EdgeIndex) :
    {e // e ∈ (fkRectTorusGraph R).edgeSet} :=
  ⟨fkRectTorusIndexedEdge R a,
    (mem_fkRectTorusGraph_edgeSet_iff R _).2 ⟨a, rfl⟩⟩

theorem fkRectEdgeToGraphEdge_bijective (R : FKRectTorus) :
    Function.Bijective (fkRectEdgeToGraphEdge R) := by
  constructor
  · intro a b h
    apply fkRectTorusIndexedEdge_injective R
    exact congrArg Subtype.val h
  · rintro ⟨e, he⟩
    obtain ⟨a, ha⟩ := (mem_fkRectTorusGraph_edgeSet_iff R e).1 he
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact ha


def fkRectEdgeGraphEquiv (R : FKRectTorus) :
    R.EdgeIndex ≃ {e // e ∈ (fkRectTorusGraph R).edgeSet} :=
  Equiv.ofBijective (fkRectEdgeToGraphEdge R)
    (fkRectEdgeToGraphEdge_bijective R)

@[simp] theorem fkRectEdgeGraphEquiv_val (R : FKRectTorus)
    (a : R.EdgeIndex) :
    (fkRectEdgeGraphEquiv R a).1 = fkRectTorusIndexedEdge R a := rfl

@[simp] theorem fkRectEdgeGraphEquiv_symm_indexedEdge
    (R : FKRectTorus)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    fkRectTorusIndexedEdge R ((fkRectEdgeGraphEquiv R).symm e) = e.1 := by
  have h := (fkRectEdgeGraphEquiv R).apply_symm_apply e
  exact congrArg Subtype.val h



abbrev FKRectGraphConfiguration (R : FKRectTorus) :=
  ConfigSpace {e // e ∈ (fkRectTorusGraph R).edgeSet}




noncomputable def fkRectFullGraphConfiguration
    (R : FKRectTorus) (omega : R.Configuration) :
    ConfigSpace (Sym2 R.Vertex) := by
  classical
  intro e
  exact if he : e ∈ (fkRectTorusGraph R).edgeSet then
    omega ((fkRectEdgeGraphEquiv R).symm ⟨e, he⟩)
  else false

@[simp] theorem fkRectFullGraphConfiguration_indexedEdge
    (R : FKRectTorus) (omega : R.Configuration) (a : R.EdgeIndex) :
    fkRectFullGraphConfiguration R omega
        (fkRectTorusIndexedEdge R a) = omega a := by
  classical
  unfold fkRectFullGraphConfiguration
  have he : fkRectTorusIndexedEdge R a ∈
      (fkRectTorusGraph R).edgeSet :=
    (mem_fkRectTorusGraph_edgeSet_iff R _).2 ⟨a, rfl⟩
  rw [dif_pos he]
  have h := (fkRectEdgeGraphEquiv R).apply_symm_apply
    ⟨fkRectTorusIndexedEdge R a, he⟩
  exact congrArg omega ((fkRectEdgeGraphEquiv R).injective
    (Subtype.ext (congrArg Subtype.val h)))

theorem fkRectFullGraphConfiguration_eq_false_of_not_edge
    (R : FKRectTorus) (omega : R.Configuration)
    {e : Sym2 R.Vertex} (he : e ∉ (fkRectTorusGraph R).edgeSet) :
    fkRectFullGraphConfiguration R omega e = false := by
  classical
  simp [fkRectFullGraphConfiguration, he]



theorem fkOpenSub_fullGraphConfiguration
    (R : FKRectTorus) (omega : R.Configuration) :
    StatMech.FK.openSub (fkRectTorusGraph R)
        (fkRectFullGraphConfiguration R omega) =
      fkRectOpenGraph R omega := by
  ext x y
  constructor
  · rintro ⟨hadj, hopen⟩
    obtain ⟨a, ha⟩ :=
      (mem_fkRectTorusGraph_edgeSet_iff R s(x, y)).1
        ((SimpleGraph.mem_edgeSet (fkRectTorusGraph R)).2 hadj)
    refine ⟨a, ?_, ha⟩
    rw [← fkRectFullGraphConfiguration_indexedEdge R omega a, ha]
    exact hopen
  · rintro ⟨a, hopen, ha⟩
    constructor
    · exact (SimpleGraph.mem_edgeSet (fkRectTorusGraph R)).1
        ((mem_fkRectTorusGraph_edgeSet_iff R _).2 ⟨a, ha⟩)
    · rw [← ha, fkRectFullGraphConfiguration_indexedEdge]
      exact hopen


def fkRectConfigurationGraphEquiv (R : FKRectTorus) :
    R.Configuration ≃ FKRectGraphConfiguration R where
  toFun omega e := omega ((fkRectEdgeGraphEquiv R).symm e)
  invFun eta a := eta (fkRectEdgeGraphEquiv R a)
  left_inv omega := by
    funext a
    simp
  right_inv eta := by
    funext e
    simp

@[simp] theorem fkRectConfigurationGraphEquiv_apply_edge
    (R : FKRectTorus) (omega : R.Configuration) (a : R.EdgeIndex) :
    fkRectConfigurationGraphEquiv R omega (fkRectEdgeGraphEquiv R a) =
      omega a := by
  simp [fkRectConfigurationGraphEquiv]



def fkRectGraphOpenGraph (R : FKRectTorus)
    (eta : FKRectGraphConfiguration R) : SimpleGraph R.Vertex where
  Adj x y := ∃ e, eta e = true ∧ e.1 = s(x, y)
  symm := by
    rintro x y ⟨e, he, hxy⟩
    exact ⟨e, he, by simpa only [Sym2.eq_swap] using hxy⟩
  loopless := ⟨by
    rintro x ⟨e, _, he⟩
    have hedgeset : s(x, x) ∈ (fkRectTorusGraph R).edgeSet := by
      exact he ▸ e.2
    exact (fkRectTorusGraph R).loopless.irrefl x
      ((SimpleGraph.mem_edgeSet (fkRectTorusGraph R)).mp hedgeset)⟩


theorem fkRectGraphOpenGraph_configurationGraphEquiv
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectGraphOpenGraph R (fkRectConfigurationGraphEquiv R omega) =
      fkRectOpenGraph R omega := by
  ext x y
  constructor
  · rintro ⟨e, he, hxy⟩
    let a := (fkRectEdgeGraphEquiv R).symm e
    refine ⟨a, ?_, ?_⟩
    · exact he
    · rw [fkRectEdgeGraphEquiv_symm_indexedEdge]
      exact hxy
  · rintro ⟨a, ha, hxy⟩
    refine ⟨fkRectEdgeGraphEquiv R a, ?_, ?_⟩
    · exact fkRectConfigurationGraphEquiv_apply_edge R omega a |>.trans ha
    · simpa using hxy



theorem fkRectGraph_clusterCount_configurationGraphEquiv
    (R : FKRectTorus) (omega : R.Configuration) :
    Fintype.card
        (fkRectGraphOpenGraph R
          (fkRectConfigurationGraphEquiv R omega)).ConnectedComponent =
      fkRectNumClusters R omega := by
  unfold fkRectNumClusters
  rw [fkRectGraphOpenGraph_configurationGraphEquiv]
  simp only [← Nat.card_eq_fintype_card]


def fkRectGraphOpenEdgeCount (R : FKRectTorus)
    (eta : FKRectGraphConfiguration R) : Nat :=
  (Finset.univ.filter fun e => eta e = true).card


theorem fkRectGraphOpenEdgeCount_configurationGraphEquiv
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectGraphOpenEdgeCount R (fkRectConfigurationGraphEquiv R omega) =
      fkRectOpenEdgeCount R omega := by
  unfold fkRectGraphOpenEdgeCount fkRectOpenEdgeCount
  symm
  apply Finset.card_bij
      (fun a _ => fkRectEdgeGraphEquiv R a)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact (fkRectConfigurationGraphEquiv_apply_edge R omega a).trans ha
  · intro a ha b hb hab
    exact (fkRectEdgeGraphEquiv R).injective hab
  · intro e he
    refine ⟨(fkRectEdgeGraphEquiv R).symm e, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      simpa [fkRectConfigurationGraphEquiv] using he
    · exact (fkRectEdgeGraphEquiv R).apply_symm_apply e


def fkRectGraphCriticalReducedWeight (R : FKRectTorus) (q : Real)
    (eta : FKRectGraphConfiguration R) : Real :=
  Real.sqrt q ^ fkRectGraphOpenEdgeCount R eta *
    q ^ Fintype.card (fkRectGraphOpenGraph R eta).ConnectedComponent



theorem fkRectGraphCriticalReducedWeight_configurationGraphEquiv
    (R : FKRectTorus) (q : Real) (omega : R.Configuration) :
    fkRectGraphCriticalReducedWeight R q
        (fkRectConfigurationGraphEquiv R omega) =
      fkRectCriticalReducedWeight R q omega := by
  unfold fkRectGraphCriticalReducedWeight fkRectCriticalReducedWeight
  rw [fkRectGraphOpenEdgeCount_configurationGraphEquiv,
    fkRectGraph_clusterCount_configurationGraphEquiv]


def fkRectGraphCriticalReducedZ (R : FKRectTorus) (q : Real) : Real :=
  ∑ eta : FKRectGraphConfiguration R,
    fkRectGraphCriticalReducedWeight R q eta


theorem fkRectGraphCriticalReducedZ_eq
    (R : FKRectTorus) (q : Real) :
    fkRectGraphCriticalReducedZ R q = fkRectCriticalReducedZ R q := by
  unfold fkRectGraphCriticalReducedZ fkRectCriticalReducedZ
  symm
  apply Fintype.sum_equiv (fkRectConfigurationGraphEquiv R)
  intro omega
  exact fkRectGraphCriticalReducedWeight_configurationGraphEquiv R q omega |>.symm


def fkRectGraphCriticalRandomClusterProb (R : FKRectTorus) (q : Real)
    (eta : FKRectGraphConfiguration R) : Real :=
  fkRectGraphCriticalReducedWeight R q eta /
    fkRectGraphCriticalReducedZ R q


theorem fkRectGraphCriticalRandomClusterProb_configurationGraphEquiv
    (R : FKRectTorus) (q : Real) (omega : R.Configuration) :
    fkRectGraphCriticalRandomClusterProb R q
        (fkRectConfigurationGraphEquiv R omega) =
      fkRectCriticalRandomClusterProb R q omega := by
  unfold fkRectGraphCriticalRandomClusterProb
    fkRectCriticalRandomClusterProb
  rw [fkRectGraphCriticalReducedWeight_configurationGraphEquiv,
    fkRectGraphCriticalReducedZ_eq]

end

end StatMech.FrontierD

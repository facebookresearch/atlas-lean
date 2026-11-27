/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.BurtonKeane.EncounterCount
public import MathlibExt.Probability.Percolation.BurtonKeane.FiniteModification
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarTopology
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanContour
public import Mathlib.Combinatorics.SimpleGraph.Ends.Properties
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Creating an encounter point

When three infinite clusters meet a box, each has an infinite branch outside it. A finite tree
inside the box connects these branches through a single encounter point. Finite-pattern absolute
continuity then gives positive encounter probability whenever infinitely many clusters have
positive probability.

The finite tree construction follows `GeneralTrifurcationPattern`, `FiniteTreeTripod`, and
`TrifurcationPatternMeasure` in the archived ATLAS statistical mechanics development.
-/

namespace MathlibExt.Probability.Percolation.BurtonKeaneWanted

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation
open MeasureTheory Filter Topology
open scoped NNReal ENNReal BigOperators

noncomputable section

/-! ## Edges incident to the box -/

section

open Finset
variable {d : ℕ}

noncomputable def incidentBoxEdges (d n : ℕ) : Finset (Sym2 (Site d)) :=
  (boxFinset d n).biUnion (fun x => (hypercubicLattice d).incidenceFinset x)

theorem mem_incidentBoxEdges (d n : ℕ) (a b : Site d) :
    s(a, b) ∈ incidentBoxEdges d n ↔
      (hypercubicLattice d).Adj a b ∧ (a ∈ box d n ∨ b ∈ box d n) := by
  simp only [incidentBoxEdges, Finset.mem_biUnion, mem_boxFinset,
    SimpleGraph.mem_incidenceFinset, SimpleGraph.mk'_mem_incidenceSet_iff]
  grind

theorem mk_mem_incidentBoxEdges {n : ℕ} {x y : Site d}
    (h : (hypercubicLattice d).Adj x y) (hm : x ∈ box d n ∨ y ∈ box d n) :
    s(x, y) ∈ incidentBoxEdges d n := (mem_incidentBoxEdges ..).mpr ⟨h, hm⟩

end

/-! ## Three clusters meeting a box -/

section

open MeasureTheory Set
open scoped ENNReal BigOperators
variable {d : ℕ}

theorem exists_three_distinct {α : Type*} {S : Set α} (h : S.encard = ⊤) :
    ∃ a b c, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have h3 : (3 : ℕ∞) ≤ S.encard := by rw [h]; exact le_top
  obtain ⟨t, hts, ht3⟩ := Set.exists_subset_encard_eq h3
  rw [Set.encard_eq_three] at ht3
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht3
  exact ⟨a, b, c, hts (by simp), hts (by simp), hts (by simp), hab, hac, hbc⟩

def threeMeetBox (d n : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | numInfiniteClusters d ω = ⊤ ∧
    ∃ x y z : Site d, x ∈ box d n ∧ y ∈ box d n ∧ z ∈ box d n ∧
      (cluster d ω x).Infinite ∧ (cluster d ω y).Infinite ∧ (cluster d ω z).Infinite ∧
      cluster d ω x ≠ cluster d ω y ∧ cluster d ω x ≠ cluster d ω z ∧
      cluster d ω y ≠ cluster d ω z}

theorem infinite_count_subset_iUnion_threeMeetBox :
    {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = ⊤}
      ⊆ ⋃ n, threeMeetBox d n := by
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  have hcard : (infiniteClusters d ω).encard = ⊤ := hω
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, h12, h13, h23⟩ := exists_three_distinct hcard
  simp only [infiniteClusters, Set.mem_ofPred_eq] at hC₁ hC₂ hC₃
  obtain ⟨hinf1, x, hxeq⟩ := hC₁
  obtain ⟨hinf2, y, hyeq⟩ := hC₂
  obtain ⟨hinf3, z, hzeq⟩ := hC₃
  have hxinf : (cluster d ω x).Infinite := by rw [← hxeq]; exact hinf1
  have hyinf : (cluster d ω y).Infinite := by rw [← hyeq]; exact hinf2
  have hzinf : (cluster d ω z).Infinite := by rw [← hzeq]; exact hinf3
  have hcl12 : cluster d ω x ≠ cluster d ω y := by rw [← hxeq, ← hyeq]; exact h12
  have hcl13 : cluster d ω x ≠ cluster d ω z := by rw [← hxeq, ← hzeq]; exact h13
  have hcl23 : cluster d ω y ≠ cluster d ω z := by rw [← hyeq, ← hzeq]; exact h23
  obtain ⟨n, hn⟩ := finite_subset_box ({x, y, z} : Set (Site d)) (Set.toFinite _)
  have hxbox : x ∈ box d n := hn (by simp)
  have hybox : y ∈ box d n := hn (by simp)
  have hzbox : z ∈ box d n := hn (by simp)
  exact Set.mem_iUnion.mpr ⟨n, hω, x, y, z, hxbox, hybox, hzbox, hxinf, hyinf, hzinf,
    hcl12, hcl13, hcl23⟩

theorem exists_threeMeetBox_pos
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hpos : 0 < μ {ω | numInfiniteClusters d ω = ⊤}) :
    ∃ n : ℕ, 0 < μ (threeMeetBox d n) := by
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hunion0 : μ (⋃ n, threeMeetBox d n) = 0 := by
    refine le_antisymm ?_ bot_le
    calc μ (⋃ n, threeMeetBox d n) ≤ ∑' n, μ (threeMeetBox d n) := measure_iUnion_le _
      _ = 0 := by simp [hcon]
  have hle : μ {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = ⊤}
      ≤ μ (⋃ n, threeMeetBox d n) :=
    measure_mono infinite_count_subset_iUnion_threeMeetBox
  rw [hunion0] at hle
  exact absurd (le_antisymm hle bot_le) (ne_of_gt hpos)

end

/-! ## A countable cover of an event of positive probability -/

section

open MeasureTheory Set
open scoped ENNReal BigOperators
variable {d : ℕ}

theorem exists_pos_of_cover {ι : Type*} [Countable ι]
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    {A : Set (ConfigSpace (Sym2 (Site d)))} {B : ι → Set (ConfigSpace (Sym2 (Site d)))}
    (hsub : A ⊆ ⋃ i, B i) (hApos : 0 < μ A) : ∃ i, 0 < μ (B i) := by
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hunion0 : μ (⋃ i, B i) = 0 := by
    refine le_antisymm ?_ bot_le
    have hsum : μ (⋃ i, B i) ≤ ∑' i, μ (B i) := measure_iUnion_le B
    have hz : ∑' i, μ (B i) = 0 := by simp [hcon]
    rw [hz] at hsum; exact hsum
  have hle : μ A ≤ μ (⋃ i, B i) := measure_mono hsub
  rw [hunion0] at hle
  exact absurd (le_antisymm hle bot_le) (ne_of_gt hApos)

end

/-! ## Sites along an open walk -/

section

open MeasureTheory Set
open scoped ENNReal BigOperators
variable {d : ℕ}

theorem support_mem_cluster (ω : ConfigSpace (Sym2 (Site d))) {a x z : Site d}
    (w : (openSubgraph d ω).Walk a x) (hz : z ∈ w.support) :
    z ∈ cluster d ω x := by
  have hza : Connected d ω a z := (w.takeUntil z hz).reachable
  rw [mem_cluster]
  exact (Connected.symm w.reachable).trans hza

end

/-! ## An infinite branch outside a finite set -/

section

open Set
variable {d : ℕ}

abbrev tailClusterVertex (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) :=
  {y : Site d // y ∈ cluster d omega x}

abbrev tailClusterGraph (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    SimpleGraph (tailClusterVertex omega x) :=
  (openSubgraph d omega).induce (cluster d omega x)

noncomputable def tailClusterCut (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (K : Finset (Site d)) : Finset (tailClusterVertex omega x) :=
  K.preimage Subtype.val Subtype.val_injective.injOn

noncomputable instance tailClusterGraphLocallyFinite
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    SimpleGraph.LocallyFinite (tailClusterGraph omega x) := by
  intro v
  let f : (tailClusterGraph omega x).neighborSet v ->
      (hypercubicLattice d).neighborSet v.1 := fun w =>
    ⟨w.1.1, (openSubgraph_le omega) w.2⟩
  exact Fintype.ofInjective f (by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (hypercubicLattice d).neighborSet v.1 => (z : Site d)) h)

instance tailClusterGraphPreconnected
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    Fact (tailClusterGraph omega x).Preconnected := ⟨by
  intro u v
  have huv : Connected d omega u.1 v.1 := (Connected.symm u.2).trans v.2
  obtain ⟨w⟩ := huv
  exact StatMech.Lattice.walk_induce_reachable (openSubgraph d omega)
    (cluster d omega x) w (fun z hz => by
      have hzx : z ∈ cluster d omega v.1 := support_mem_cluster omega w hz
      rwa [← cluster_eq_of_connected v.2] at hzx) u.2 v.2⟩

theorem infiniteCluster_component_after_finset
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d omega x).Infinite) (K : Finset (Site d)) :
    ∃ D : (tailClusterGraph omega x).ComponentCompl (tailClusterCut omega x K),
      D.supp.Infinite := by
  let : Infinite (tailClusterVertex omega x) := hinf.to_subtype
  let e : (tailClusterGraph omega x).end :=
    ⟨(SimpleGraph.nonempty_ends_of_infinite (tailClusterGraph omega x)).choose,
      (SimpleGraph.nonempty_ends_of_infinite (tailClusterGraph omega x)).choose_spec⟩
  let D : (tailClusterGraph omega x).ComponentCompl (tailClusterCut omega x K) :=
    (e : (j : (Finset (tailClusterVertex omega x))ᵒᵖ) →
      (tailClusterGraph omega x).componentComplFunctor.obj j)
      (Opposite.op (tailClusterCut omega x K))
  exact ⟨D, SimpleGraph.end_componentCompl_infinite
    (tailClusterGraph omega x) e (Opposite.op (tailClusterCut omega x K))⟩

def tailComponentSites (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (K : Finset (Site d))
    (D : (tailClusterGraph omega x).ComponentCompl (tailClusterCut omega x K)) :
    Set (Site d) := Subtype.val '' (D : Set (tailClusterVertex omega x))

theorem tailComponentSites_infinite
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) (K : Finset (Site d))
    (D : (tailClusterGraph omega x).ComponentCompl (tailClusterCut omega x K))
    (hD : D.supp.Infinite) : (tailComponentSites omega x K D).Infinite := by
  exact hD.image Subtype.val_injective.injOn

theorem tailComponentSites_subset_cluster
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) (K : Finset (Site d))
    (D : (tailClusterGraph omega x).ComponentCompl (tailClusterCut omega x K)) :
    tailComponentSites omega x K D ⊆ cluster d omega x := by
  rintro _ ⟨y, _, rfl⟩
  exact y.2

theorem tailComponentSites_connected_outside
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) (K : Finset (Site d))
    (D : (tailClusterGraph omega x).ComponentCompl (tailClusterCut omega x K)) :
    ∀ u ∈ tailComponentSites omega x K D,
      ∀ v ∈ tailComponentSites omega x K D,
        ∃ (hu : u ∉ (K : Set (Site d))) (hv : v ∉ (K : Set (Site d))),
          ((openSubgraph d omega).induce (K : Set (Site d))ᶜ).Reachable
            ⟨u, hu⟩ ⟨v, hv⟩ := by
  rintro u ⟨uC, huD, rfl⟩ v ⟨vC, hvD, rfl⟩
  rcases huD with ⟨huCut, huComp⟩
  rcases hvD with ⟨hvCut, hvComp⟩
  have huK : uC.1 ∉ (K : Set (Site d)) := by
    intro hmem
    exact huCut (by simp [tailClusterCut, hmem])
  have hvK : vC.1 ∉ (K : Set (Site d)) := by
    intro hmem
    exact hvCut (by simp [tailClusterCut, hmem])
  refine ⟨huK, hvK, ?_⟩
  have hreach :
      ((tailClusterGraph omega x).induce
        ((tailClusterCut omega x K : Set (tailClusterVertex omega x)))ᶜ).Reachable
          ⟨uC, huCut⟩ ⟨vC, hvCut⟩ := by
    rw [← SimpleGraph.ConnectedComponent.eq]
    exact huComp.trans hvComp.symm
  let f0 : {z : tailClusterVertex omega x //
      z ∈ ((tailClusterCut omega x K : Set (tailClusterVertex omega x)))ᶜ} →
      {z : Site d // z ∈ (K : Set (Site d))ᶜ} := fun z =>
    ⟨z.1.1, by
      intro hzK
      exact z.2 (by simp [tailClusterCut, hzK])⟩
  let f : ((tailClusterGraph omega x).induce
      ((tailClusterCut omega x K : Set (tailClusterVertex omega x)))ᶜ) →g
      ((openSubgraph d omega).induce (K : Set (Site d))ᶜ) := {
    toFun := f0
    map_rel' := by
      intro a b hab
      exact hab
  }
  exact hreach.map f

theorem infiniteCluster_has_open_exit_to_infinite_tail
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d omega x).Infinite) (K : Finset (Site d))
    (hxK : x ∈ K) :
    ∃ u v : Site d, ∃ T : Set (Site d),
      u ∈ K ∧ v ∉ K ∧ (openSubgraph d omega).Adj u v ∧ v ∈ T ∧
      T.Infinite ∧ T ⊆ cluster d omega x ∧
      (∀ a ∈ T, ∀ b ∈ T,
        ∃ (ha : a ∉ (K : Set (Site d))) (hb : b ∉ (K : Set (Site d))),
          ((openSubgraph d omega).induce (K : Set (Site d))ᶜ).Reachable
            ⟨a, ha⟩ ⟨b, hb⟩) := by
  obtain ⟨D, hD⟩ := infiniteCluster_component_after_finset omega x hinf K
  have hcut : (tailClusterCut omega x K).Nonempty := by
    refine ⟨⟨x, self_mem_cluster omega x⟩, ?_⟩
    simp [tailClusterCut, hxK]
  obtain ⟨⟨v, u⟩, hvD, huCut, hadj⟩ :=
    D.exists_adj_boundary_pair (tailClusterGraphPreconnected omega x).out hcut
  have huK : u.1 ∈ K := by
    simpa [tailClusterCut] using huCut
  have hvK : v.1 ∉ K := by
    intro hv
    exact D.notMem_of_mem hvD (by simp [tailClusterCut, hv])
  refine ⟨u.1, v.1, tailComponentSites omega x K D,
    huK, hvK, hadj.symm, ⟨v, hvD, rfl⟩, ?_, ?_, ?_⟩
  · exact tailComponentSites_infinite omega x K D hD
  · exact tailComponentSites_subset_cluster omega x K D
  · exact tailComponentSites_connected_outside omega x K D

structure InfiniteClusterTailData (omega : ConfigSpace (Sym2 (Site d)))
    (K : Finset (Site d)) (x : Site d) where
  inside : Site d
  outside : Site d
  tail : Set (Site d)
  inside_mem : inside ∈ K
  outside_not_mem : outside ∉ K
  exit_open : (openSubgraph d omega).Adj inside outside
  outside_mem_tail : outside ∈ tail
  tail_infinite : tail.Infinite
  tail_subset_cluster : tail ⊆ cluster d omega x
  tail_connected_outside :
    ∀ a ∈ tail, ∀ b ∈ tail,
      ∃ (ha : a ∉ (K : Set (Site d))) (hb : b ∉ (K : Set (Site d))),
        ((openSubgraph d omega).induce (K : Set (Site d))ᶜ).Reachable
          ⟨a, ha⟩ ⟨b, hb⟩

noncomputable def infiniteClusterTailData
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d omega x).Infinite) (K : Finset (Site d))
    (hxK : x ∈ K) : InfiniteClusterTailData omega K x := by
  classical
  exact Classical.choice (by
    obtain ⟨u, v, T, hu, hv, huv, hvT, hTinf, hTsub, hTconn⟩ :=
      infiniteCluster_has_open_exit_to_infinite_tail omega x hinf K hxK
    exact ⟨⟨u, v, T, hu, hv, huv, hvT, hTinf, hTsub, hTconn⟩⟩)

end

/-! ## Tripods in finite trees -/

section

open Set SimpleGraph Finset

theorem tree_two_leaves {V : Type*} [Fintype V] (T : SimpleGraph V)
    [DecidableRel T.Adj] (hT : T.IsTree) (hn : 2 ≤ Fintype.card V) :
    ∃ a b : V, a ≠ b ∧ T.degree a = 1 ∧ T.degree b = 1 := by
  classical
  have hNontriv : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  have hpos : ∀ v : V, 1 ≤ T.degree v := by
    intro v
    have := hT.connected.preconnected.minDegree_pos_of_nontrivial (G := T)
    exact le_trans this (T.minDegree_le_degree v)
  have hsum : ∑ v : V, T.degree v = 2 * #T.edgeFinset :=
    T.sum_degrees_eq_twice_card_edges
  have hedge : #T.edgeFinset + 1 = Fintype.card V := hT.card_edgeFinset
  by_contra hcon
  push Not at hcon
  have hleaf_sub : ∀ a b : V, T.degree a = 1 → T.degree b = 1 → a = b := by
    intro a b ha hb
    by_contra hab
    exact hcon a b hab ha hb
  obtain ⟨v0, hv0⟩ := hT.exists_vert_degree_one_of_nontrivial
  have hlower : 2 * Fintype.card V - 1 ≤ ∑ v : V, T.degree v := by
    have hbound : ∀ v : V, (if v = v0 then 1 else 2) ≤ T.degree v := by
      intro v
      by_cases hvv : v = v0
      · subst hvv
        simp [hv0]
      · simp only [ite_eq_right hvv]
        rcases Nat.lt_or_ge (T.degree v) 2 with hlt | hge
        · have h1 : T.degree v = 1 := by have := hpos v; omega
          exact absurd (hleaf_sub v v0 h1 hv0) hvv
        · exact hge
    have hconst : (∑ v : V, if v = v0 then (1 : ℕ) else 2) + 1 =
        2 * Fintype.card V := by
      have hstep : (∑ v : V, (if v = v0 then (1 : ℕ) else 2)) + 1 =
          ∑ v : V, ((if v = v0 then (1 : ℕ) else 2) +
            (if v = v0 then 1 else 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ v0]
        simp
      rw [hstep]
      have htwo : ∀ v : V,
          (if v = v0 then (1 : ℕ) else 2) + (if v = v0 then 1 else 0) = 2 := by
        intro v
        by_cases hvv : v = v0 <;> simp [hvv]
      rw [Finset.sum_congr rfl (fun v _ => htwo v), Finset.sum_const,
        Finset.card_univ, smul_eq_mul, mul_comm]
    have hsumif : (∑ v : V, (if v = v0 then (1 : ℕ) else 2)) ≤
        ∑ v : V, T.degree v :=
      Finset.sum_le_sum (fun v _ => hbound v)
    omega
  omega

theorem branch_vertex_of_three_leaves {V : Type*} [Fintype V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : T.degree a = 1) (hb : T.degree b = 1) (hc : T.degree c = 1) :
    ∃ u : V, 3 ≤ T.degree u := by
  classical
  by_contra hbranch
  push Not at hbranch
  let L : Finset V := {a, b, c}
  have hLcard : L.card = 3 := by simp [L, hab, hac, hbc]
  have hbound : ∀ v : V,
      T.degree v + (if v ∈ L then 1 else 0) ≤ 2 := by
    intro v
    by_cases hv : v ∈ L
    · simp only [L, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · simp [L, ha]
      · simp [L, hb]
      · simp [L, hc]
    · simp only [ite_eq_right hv, add_zero]
      have := hbranch v
      omega
  have hsum_bound :
      (∑ v : V, (T.degree v + (if v ∈ L then 1 else 0))) ≤
        ∑ _v : V, 2 :=
    Finset.sum_le_sum (fun v _ => hbound v)
  have hind : (∑ v : V, if v ∈ L then 1 else 0) = L.card := by
    rw [Finset.sum_boole]
    simp
  have hdeg : ∑ v : V, T.degree v = 2 * T.edgeFinset.card :=
    T.sum_degrees_eq_twice_card_edges
  have hedge : T.edgeFinset.card + 1 = Fintype.card V := hT.card_edgeFinset
  have htwoSum : (∑ _v : V, (2 : ℕ)) = 2 * Fintype.card V := by
    simp [mul_comm]
  rw [Finset.sum_add_distrib, hind, hLcard, hdeg, htwoSum, ← hedge] at hsum_bound
  omega

theorem not_mem_support_of_isolated {V : Type*} {G : SimpleGraph V} {u : V}
    (hiso : ∀ z, ¬ G.Adj u z) : ∀ {a b : V} (w : G.Walk a b), a ≠ u → u ∉ w.support := by
  intro a b w
  induction w with
  | nil => intro ha; simpa using ha.symm
  | @cons a v b hav w ih =>
      intro ha
      have hv : v ≠ u := fun hvu => hiso a (hvu ▸ hav.symm)
      simp only [Walk.support_cons, List.mem_cons, not_or]
      exact ⟨fun h => ha h.symm, ih hv⟩

theorem neighbors_separated {V : Type*} (G : SimpleGraph V) (hG : G.IsAcyclic)
    {u a b : V} (hua : G.Adj u a) (hub : G.Adj u b) (hab : a ≠ b) :
    ¬ (G.deleteIncidenceSet u).Reachable a b := by
  classical
  rintro ⟨w⟩
  have hle : G.deleteIncidenceSet u ≤ G := G.deleteIncidenceSet_le u
  have hiso : ∀ z, ¬ (G.deleteIncidenceSet u).Adj u z :=
    fun z h => (deleteIncidenceSet_adj.mp h).2.1 rfl
  have hnotin : u ∉ w.support :=
    not_mem_support_of_isolated hiso w hua.symm.ne
  have hnotin_map : u ∉ (w.mapLe hle).support := by
    rw [Walk.support_mapLe_eq_support hle w]
    exact hnotin
  set p : G.Path a b := (w.mapLe hle).toPath
  have hp_notin : u ∉ p.1.support := by
    intro hu
    exact hnotin_map (Walk.support_toPath_subset_support _ hu)
  have hbne : u ≠ b := hub.ne
  have haune : a ≠ u := hua.symm.ne
  have qpath : (Walk.cons hua.symm (Walk.cons hub Walk.nil)).IsPath := by
    rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff]
    refine ⟨⟨Walk.IsPath.nil, ?_⟩, ?_⟩
    · simpa using hbne
    · simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, not_or]
      exact ⟨haune, hab, by simp⟩
  set q : G.Path a b := ⟨_, qpath⟩
  have hq_in : u ∈ q.1.support := by
    simp [q]
  have huniq := (hG.subsingleton_path _ _).elim p q
  rw [huniq] at hp_notin
  exact hp_notin hq_in

theorem leaf_in_neighbor_branch {V : Type*} [Fintype V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) {u v : V}
    (huv : T.Adj u v) :
    ∃ l : V, T.degree l = 1 ∧ (T.deleteIncidenceSet u).Reachable v l := by
  classical
  let H := T.deleteIncidenceSet u
  let C : Set V := {x | H.Reachable v x}
  let K : SimpleGraph C := H.induce C
  have hvu : v ≠ u := huv.ne'
  have hu_not_C : u ∉ C := by
    intro huC
    have hr : H.Reachable v u := huC
    obtain ⟨p⟩ := hr
    have hiso : ∀ z, ¬ H.Adj u z :=
      fun z h => (deleteIncidenceSet_adj.mp h).2.1 rfl
    exact (not_mem_support_of_isolated hiso p hvu) (by simp)
  have hKconn : K.Connected := by
    rw [connected_iff]
    refine ⟨?_, ⟨v, Reachable.refl v⟩⟩
    intro a b
    have hav : H.Reachable v a := a.2
    have hbv : H.Reachable v b := b.2
    obtain ⟨pa⟩ := hav
    obtain ⟨pb⟩ := hbv
    let q := pa.reverse.append pb
    have hqC : ∀ x ∈ q.support, x ∈ C := by
      intro x hx
      exact ⟨pa.append (q.takeUntil x hx)⟩
    exact ⟨q.induce C hqC⟩
  have hKacyc : K.IsAcyclic :=
    (hT.isAcyclic.anti (T.deleteIncidenceSet_le u)).induce C
  have hKtree : K.IsTree := ⟨hKconn, hKacyc⟩
  have hCclosed : ∀ {x y : V}, H.Adj x y → x ∈ C → y ∈ C := by
    intro x y hxy hx
    exact hx.trans hxy.reachable
  have hKdegree (x : C) : K.degree x = H.degree x.1 := by
    change (H.induce C).degree x = H.degree x.1
    apply SimpleGraph.degree_induce_of_neighborSet_subset
    intro y hy
    exact hCclosed (SimpleGraph.mem_neighborSet H x.1 y |>.mp hy) x.2
  by_cases hcard : Fintype.card C = 1
  · refine ⟨v, ?_, Reachable.refl v⟩
    rw [degree_eq_one_iff_existsUnique_adj]
    refine ⟨u, huv.symm, ?_⟩
    intro z hvz
    by_cases hzu : z = u
    · exact hzu
    · have hvzH : H.Adj v z := deleteIncidenceSet_adj.mpr ⟨hvz, hvu, hzu⟩
      have hzC : z ∈ C := hvzH.reachable
      have hsub : Subsingleton C := Fintype.card_le_one_iff_subsingleton.mp (by omega)
      have : (z : V) = v := congrArg Subtype.val
        (hsub.elim ⟨z, hzC⟩ ⟨v, Reachable.refl v⟩)
      exact absurd this hvz.ne'
  · have hcard2 : 2 ≤ Fintype.card C := by
      have hpos : 0 < Fintype.card C := Fintype.card_pos_iff.mpr ⟨v, Reachable.refl v⟩
      omega
    obtain ⟨a, b, hab, ha, hb⟩ := tree_two_leaves K hKtree hcard2
    have hchoice : ∃ l : C, l.1 ≠ v ∧ K.degree l = 1 := by
      by_cases hav : a.1 = v
      · refine ⟨b, ?_, hb⟩
        intro hbv
        exact hab (Subtype.ext (hav.trans hbv.symm))
      · exact ⟨a, hav, ha⟩
    obtain ⟨l, hlv, hlK⟩ := hchoice
    have hlu : l.1 ≠ u := fun h => hu_not_C (h ▸ l.2)
    have hnotadj_u : ¬ T.Adj u l.1 := by
      intro hul
      exact neighbors_separated T hT.isAcyclic huv hul (fun h => hlv h.symm) l.2
    have hlH : H.degree l.1 = 1 := by
      rw [← hKdegree l]
      exact hlK
    have hlT : T.degree l.1 = 1 := by
      rw [degree_eq_one_iff_existsUnique_adj] at hlH ⊢
      obtain ⟨z, hlz, hzuniq⟩ := hlH
      refine ⟨z, (deleteIncidenceSet_adj.mp hlz).1, ?_⟩
      intro z' hlz'
      have hz'u : z' ≠ u := by
        intro h
        subst z'
        exact hnotadj_u hlz'.symm
      exact hzuniq z' (deleteIncidenceSet_adj.mpr ⟨hlz', hlu, hz'u⟩)
    exact ⟨l.1, hlT, l.2⟩

theorem exists_tripod_with_stems {V : Type*} [Fintype V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) {u : V}
    (hu : 3 ≤ T.degree u) :
    ∃ stem leaf : Fin 3 → V,
      Function.Injective stem ∧
      (∀ i, T.Adj u (stem i)) ∧
      Function.Injective leaf ∧
      (∀ i, T.degree (leaf i) = 1) ∧
      (∀ i, (T.deleteIncidenceSet u).Reachable (stem i) (leaf i)) ∧
      (∀ i j, i ≠ j →
        ¬ (T.deleteIncidenceSet u).Reachable (leaf i) (leaf j)) := by
  classical
  have hcard : Fintype.card (Fin 3) ≤
      Fintype.card {x // x ∈ T.neighborFinset u} := by
    rw [Fintype.card_fin, Fintype.card_coe,
      SimpleGraph.card_neighborFinset_eq_degree]
    exact hu
  obtain ⟨n⟩ : Nonempty (Fin 3 ↪ {x // x ∈ T.neighborFinset u}) :=
    Function.Embedding.nonempty_iff_card_le.mpr hcard
  let stem : Fin 3 → V := fun i => (n i).1
  have hstemAdj : ∀ i, T.Adj u (stem i) := fun i =>
    (SimpleGraph.mem_neighborFinset T u (stem i)).mp (n i).2
  have hstemInj : Function.Injective stem := fun i j hij =>
    n.injective (Subtype.ext hij)
  choose leaf hleaf hreach using fun i =>
    leaf_in_neighbor_branch T hT (hstemAdj i)
  have hsep : ∀ i j, i ≠ j →
      ¬ (T.deleteIncidenceSet u).Reachable (leaf i) (leaf j) := by
    intro i j hij hlij
    have hstemNe : stem i ≠ stem j := fun h => hij (hstemInj h)
    have hr : (T.deleteIncidenceSet u).Reachable (stem i) (stem j) :=
      (hreach i).trans (hlij.trans (hreach j).symm)
    exact neighbors_separated T hT.isAcyclic
      (hstemAdj i) (hstemAdj j) hstemNe hr
  have hleafInj : Function.Injective leaf := by
    intro i j hij
    by_contra hne
    exact hsep i j hne (hij ▸ Reachable.refl (leaf i))
  exact ⟨stem, leaf, hstemInj, hstemAdj, hleafInj, hleaf, hreach, hsep⟩

end

/-! ## Pruning leaves away from the boundary -/

section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
variable {d : ℕ}

theorem leaf_has_neighbour {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v : V} (hv : G.degree v = 1) : ∃ w, G.Adj v w := by
  classical
  have : (G.neighborFinset v).Nonempty := by
    rw [← Finset.card_pos, SimpleGraph.card_neighborFinset_eq_degree, hv]; exact one_pos
  obtain ⟨w, hw⟩ := this
  exact ⟨w, (SimpleGraph.mem_neighborFinset _ _ _).mp hw⟩

theorem leaf_neighbour_unique {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v w w' : V} (hv : G.degree v = 1) (hw : G.Adj v w) (hw' : G.Adj v w') :
    w = w' := by
  classical
  have hcard : (G.neighborFinset v).card = 1 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hv
  have hmemw : w ∈ G.neighborFinset v := (SimpleGraph.mem_neighborFinset _ _ _).mpr hw
  have hmemw' : w' ∈ G.neighborFinset v := (SimpleGraph.mem_neighborFinset _ _ _).mpr hw'
  exact Finset.card_le_one.mp (le_of_eq hcard) w hmemw w' hmemw'

theorem leaf_delete_reachable {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v w : V} (hdeg : G.degree v = 1) (hvw : G.Adj v w)
    {a b : V} (ha : a ≠ v) (hb : b ≠ v) (hreach : G.Reachable a b) :
    (G.deleteEdges {s(v, w)}).Reachable a b := by
  classical
  obtain ⟨p⟩ := hreach
  suffices H : ∀ (n : ℕ) {x y : V} (q : G.Walk x y), q.length ≤ n → x ≠ v → y ≠ v →
      (G.deleteEdges {s(v, w)}).Reachable x y by
    exact H p.length p le_rfl ha hb
  intro n
  induction n with
  | zero =>
    intro x y q hlen hx hy
    rw [Nat.le_zero, SimpleGraph.Walk.length_eq_zero_iff] at hlen
    cases hlen; exact Reachable.refl _
  | succ n ih =>
    intro x y q hlen hx hy
    cases q with
    | nil => exact Reachable.refl _
    | @cons x c y hxc r =>
      have hrlen : r.length ≤ n := by
        simp only [SimpleGraph.Walk.length_cons] at hlen; omega
      by_cases hcv : c = v
      · have hxv : G.Adj x v := hcv ▸ hxc
        have hxw : x = w := (leaf_neighbour_unique G hdeg hvw hxv.symm).symm
        cases r with
        | nil => rw [hcv] at hy; exact absurd rfl hy
        | @cons c e y hce s =>
          have hve : G.Adj v e := hcv ▸ hce
          have hew : e = w := (leaf_neighbour_unique G hdeg hvw hve).symm
          have hene : e ≠ v := by rw [hew]; exact hvw.ne'
          have hslen : s.length ≤ n := by
            simp only [SimpleGraph.Walk.length_cons] at hrlen; omega
          have hr : (G.deleteEdges {s(v, w)}).Reachable e y := ih s hslen hene hy
          have hxe : x = e := by rw [hxw, hew]
          rw [hxe]; exact hr
      · have hedge : (G.deleteEdges {s(v, w)}).Adj x c := by
          rw [SimpleGraph.deleteEdges_adj]
          refine ⟨hxc, ?_⟩
          intro hmem
          rw [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
          rcases hmem with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact hx h1
          · exact hcv h2
        exact (hedge.reachable).trans (ih r hrlen hcv hy)

theorem deleteEdge_card_lt {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v w : V} (hvw : G.Adj v w)
    [DecidableRel (G.deleteEdges {s(v, w)}).Adj] :
    (G.deleteEdges {s(v, w)}).edgeFinset.card < G.edgeFinset.card := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (SimpleGraph.edgeFinset_mono (SimpleGraph.deleteEdges_le _))]
  refine ⟨s(v, w), (SimpleGraph.mem_edgeFinset).mpr hvw, ?_⟩
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges]
  intro hmem
  exact hmem.2 (Set.mem_singleton _)

theorem deleteEdge_acyclic {V : Type*} (G : SimpleGraph V) (hacyc : G.IsAcyclic)
    (s : Set (Sym2 V)) : (G.deleteEdges s).IsAcyclic :=
  hacyc.anti (SimpleGraph.deleteEdges_le s)

theorem boundaryAnchored_subforest {V : Type*} [Fintype V] (G : SimpleGraph V)
    (B : V → Prop) (hacyc : G.IsAcyclic) :
    ∃ (F : SimpleGraph V) (_ : DecidableRel F.Adj),
      F ≤ G ∧ F.IsAcyclic ∧ (∀ v, F.degree v = 1 → B v) ∧
      (∀ a b, B a → B b → G.Reachable a b → F.Reachable a b) := by
  classical
  suffices H : ∀ (n : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj], G.IsAcyclic →
      G.edgeFinset.card ≤ n →
      ∃ (F : SimpleGraph V) (_ : DecidableRel F.Adj),
        F ≤ G ∧ F.IsAcyclic ∧ (∀ v, F.degree v = 1 → B v) ∧
        (∀ a b, B a → B b → G.Reachable a b → F.Reachable a b) by
    exact H G.edgeFinset.card G hacyc le_rfl
  intro n
  induction n with
  | zero =>
    intro G _ hac hcard
    refine ⟨G, inferInstance, le_refl G, hac, ?_, fun a b _ _ h => h⟩
    intro v hv
    exfalso
    obtain ⟨w, hvw⟩ := leaf_has_neighbour G hv
    have : 1 ≤ G.edgeFinset.card := by
      apply Finset.card_pos.mpr
      exact ⟨s(v, w), (SimpleGraph.mem_edgeFinset).mpr hvw⟩
    omega
  | succ n ih =>
    intro G _ hac hcard
    by_cases hbad : ∃ v, G.degree v = 1 ∧ ¬ B v
    · obtain ⟨v, hvdeg, hvB⟩ := hbad
      obtain ⟨w, hvw⟩ := leaf_has_neighbour G hvdeg
      have hG'ac : (G.deleteEdges {s(v, w)}).IsAcyclic := deleteEdge_acyclic G hac _
      have hlt : (G.deleteEdges {s(v, w)}).edgeFinset.card < G.edgeFinset.card :=
        deleteEdge_card_lt G hvw
      have hle' : (G.deleteEdges {s(v, w)}).edgeFinset.card ≤ n := by omega
      obtain ⟨F, hFdec, hFle, hFac, hFleaf, hFpres⟩ :=
        ih (G.deleteEdges {s(v, w)}) hG'ac hle'
      refine ⟨F, hFdec, le_trans hFle (SimpleGraph.deleteEdges_le _), hFac, hFleaf, ?_⟩
      intro a b hBa hBb hab
      apply hFpres a b hBa hBb
      have hav : a ≠ v := fun h => hvB (h ▸ hBa)
      have hbv : b ≠ v := fun h => hvB (h ▸ hBb)
      exact leaf_delete_reachable G hvdeg hvw hav hbv hab
    · simp only [not_exists, not_and, not_not] at hbad
      exact ⟨G, inferInstance, le_refl G, hac, fun v hv => hbad v hv, fun a b _ _ h => h⟩

end

/-! ## Three prescribed leaves in a connected graph -/

section

open Set SimpleGraph Finset

theorem degree_pos_of_two_vertices {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    {x y : V} (hxy : x ≠ y) : 1 ≤ G.degree x := by
  have hr := hG.preconnected x y
  have hex : ∃ z, G.Adj x z := by
    obtain ⟨w⟩ := hr
    cases w with
    | nil => exact absurd rfl hxy
    | cons h _ => exact ⟨_, h⟩
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, G.degree_pos_iff_exists_adj]
  exact hex

theorem degree_pos_of_reachable_ne {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V}
    (hr : G.Reachable x y) (hxy : x ≠ y) : 1 ≤ G.degree x := by
  have hex : ∃ z, G.Adj x z := by
    obtain ⟨w⟩ := hr
    cases w with
    | nil => exact absurd rfl hxy
    | cons h _ => exact ⟨_, h⟩
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, G.degree_pos_iff_exists_adj]
  exact hex

theorem degree_le_of_subgraph {V : Type*} [Fintype V]
    {F G : SimpleGraph V} [DecidableRel F.Adj] [DecidableRel G.Adj]
    (hFG : F ≤ G) (x : V) : F.degree x ≤ G.degree x := by
  rw [← F.card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro y hy
  rw [SimpleGraph.mem_neighborFinset] at hy ⊢
  exact hFG hy

theorem three_pendant_vertices_have_tripod {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (p : Fin 3 → V) (hpinj : Function.Injective p)
    (hpdeg : ∀ i, G.degree (p i) = 1) :
    ∃ (C : Set V) (T : SimpleGraph C) (_ : DecidableRel T.Adj)
      (hub : C) (stem leaf : Fin 3 → C),
      T.IsTree ∧
      (∀ a b, T.Adj a b → G.Adj a.1 b.1) ∧
      Function.Injective stem ∧
      (∀ i, T.Adj hub (stem i)) ∧
      Function.Injective leaf ∧
      (∀ i, ∃ j, (leaf i).1 = p j) ∧
      (∀ i, (T.deleteIncidenceSet hub).Reachable (stem i) (leaf i)) ∧
      (∀ i, T.Reachable hub (leaf i)) ∧
      (∀ i j, i ≠ j →
        ¬ (T.deleteIncidenceSet hub).Reachable (leaf i) (leaf j)) := by
  classical
  obtain ⟨S, hSG, hStree⟩ := hG.exists_isTree_le
  let : DecidableRel S.Adj := Classical.decRel _
  have hpSdeg : ∀ i, S.degree (p i) = 1 := by
    intro i
    have hj : ∃ j : Fin 3, i ≠ j := by
      fin_cases i
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
    obtain ⟨j, hij⟩ := hj
    have hpne : p i ≠ p j := fun h => hij (hpinj h)
    have hlo : 1 ≤ S.degree (p i) :=
      degree_pos_of_two_vertices S hStree.connected hpne
    have hhi : S.degree (p i) ≤ 1 := by
      rw [← hpdeg i]
      exact degree_le_of_subgraph hSG (p i)
    omega
  let B : V → Prop := fun v => ∃ i, p i = v
  let : DecidablePred B := Classical.decPred _
  obtain ⟨F, hFdec, hFS, hFac, hFleaf, hFpres⟩ :=
    boundaryAnchored_subforest S B hStree.isAcyclic
  let : DecidableRel F.Adj := hFdec
  have hpFreach : ∀ i j, F.Reachable (p i) (p j) := by
    intro i j
    apply hFpres (p i) (p j) ⟨i, rfl⟩ ⟨j, rfl⟩
    exact hStree.connected.preconnected _ _
  have hpFdeg : ∀ i, F.degree (p i) = 1 := by
    intro i
    obtain ⟨j, hij⟩ : ∃ j : Fin 3, i ≠ j := by
      fin_cases i
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
    have hpne : p i ≠ p j := fun h => hij (hpinj h)
    have hlo : 1 ≤ F.degree (p i) :=
      degree_pos_of_reachable_ne F (hpFreach i j) hpne
    have hhi : F.degree (p i) ≤ 1 := by
      rw [← hpSdeg i]
      exact degree_le_of_subgraph hFS (p i)
    omega
  let C : Set V := {v | F.Reachable (p 0) v}
  let T : SimpleGraph C := F.induce C
  have hpC : ∀ i, p i ∈ C := fun i => hpFreach 0 i
  have hCclosed : ∀ {x y : V}, F.Adj x y → x ∈ C → y ∈ C := by
    intro x y hxy hx
    exact hx.trans hxy.reachable
  have hTconn : T.Connected := by
    rw [connected_iff]
    refine ⟨?_, ⟨p 0, hpC 0⟩⟩
    intro a b
    obtain ⟨pa⟩ := a.2
    obtain ⟨pb⟩ := b.2
    let q := pa.reverse.append pb
    have hqC : ∀ x ∈ q.support, x ∈ C := by
      intro x hx
      exact ⟨pa.append (q.takeUntil x hx)⟩
    exact ⟨q.induce C hqC⟩
  have hTac : T.IsAcyclic := hFac.induce C
  have hTtree : T.IsTree := ⟨hTconn, hTac⟩
  have hTdegree (x : C) : T.degree x = F.degree x.1 := by
    change (F.induce C).degree x = F.degree x.1
    apply SimpleGraph.degree_induce_of_neighborSet_subset
    intro y hy
    exact hCclosed (SimpleGraph.mem_neighborSet F x.1 y |>.mp hy) x.2
  let pc : Fin 3 → C := fun i => ⟨p i, hpC i⟩
  have hpcinj : Function.Injective pc := fun i j h =>
    hpinj (congrArg Subtype.val h)
  have hpcdeg : ∀ i, T.degree (pc i) = 1 := by
    intro i
    rw [hTdegree]
    exact hpFdeg i
  obtain ⟨hub, hhub⟩ := branch_vertex_of_three_leaves T hTtree
    (fun h => (by decide : (0 : Fin 3) ≠ 1) (hpcinj h))
    (fun h => (by decide : (0 : Fin 3) ≠ 2) (hpcinj h))
    (fun h => (by decide : (1 : Fin 3) ≠ 2) (hpcinj h))
    (hpcdeg 0) (hpcdeg 1) (hpcdeg 2)
  obtain ⟨stem, leaf, hsteminj, hstemadj, hleafinj, hleafdeg,
      hstemleaf, hleafcut⟩ :=
    exists_tripod_with_stems T hTtree hhub
  have hleaf_terminal : ∀ i, ∃ j, (leaf i).1 = p j := by
    intro i
    have hFdeg1 : F.degree (leaf i).1 = 1 := by
      rw [← hTdegree (leaf i)]
      exact hleafdeg i
    obtain ⟨j, hj⟩ := hFleaf (leaf i).1 hFdeg1
    exact ⟨j, hj.symm⟩
  refine ⟨C, T, inferInstance, hub, stem, leaf, hTtree, ?_, hsteminj,
    hstemadj, hleafinj, hleaf_terminal, hstemleaf, ?_, hleafcut⟩
  · intro a b hab
    exact hSG (hFS hab)
  · intro i
    exact hTtree.connected.preconnected _ _

end

/-! ## Connecting three exits of a lattice box -/

section

open Set SimpleGraph Finset
variable {d n : ℕ}

abbrev ThreeExitVertex (d n : ℕ) :=
  Sum (↑(boxFinset d n) : Type) (Fin 3)

def threeExitGraph (inside : Fin 3 → Site d) :
    SimpleGraph (ThreeExitVertex d n) where
  Adj a b := match a, b with
    | Sum.inl x, Sum.inl y => (hypercubicLattice d).Adj x.1 y.1
    | Sum.inl x, Sum.inr i => x.1 = inside i
    | Sum.inr i, Sum.inl x => x.1 = inside i
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨by
    intro a b
    cases a <;> cases b <;> simp_all [adj_comm]⟩
  loopless := ⟨by
    rintro (x | i)
    · exact (hypercubicLattice d).irrefl
    · simp⟩

instance instDecidableThreeExitAdj (inside : Fin 3 → Site d) :
    DecidableRel (threeExitGraph (n := n) inside).Adj :=
  fun a b => by cases a <;> cases b <;> dsimp [threeExitGraph] <;> infer_instance

def threeExitTip (i : Fin 3) : ThreeExitVertex d n := Sum.inr i

theorem threeExitTip_injective :
    Function.Injective (threeExitTip (d := d) (n := n)) := Sum.inr_injective

theorem threeExitTip_degree_one (inside : Fin 3 → Site d)
    (hinside : ∀ i, inside i ∈ box d n) (i : Fin 3) :
    (threeExitGraph (n := n) inside).degree (threeExitTip i) = 1 := by
  classical
  rw [degree_eq_one_iff_existsUnique_adj]
  let q : ↑(boxFinset d n) := ⟨inside i, by simpa [boxFinset] using hinside i⟩
  refine ⟨Sum.inl q, by simp [threeExitGraph, threeExitTip, q], ?_⟩
  intro z hz
  rcases z with z | j
  · simp only [threeExitGraph] at hz
    exact congrArg Sum.inl (Subtype.ext hz)
  · simp [threeExitGraph, threeExitTip] at hz

theorem threeExitGraph_core_reachable (inside : Fin 3 → Site d)
    {x y : ↑(boxFinset d n)} :
    (threeExitGraph inside).Reachable (Sum.inl x) (Sum.inl y) := by
  let f : (hypercubicLattice d).induce (box d n) →g threeExitGraph inside :=
    { toFun := fun z => Sum.inl ⟨z.1, mem_boxFinset.mpr z.2⟩
      map_rel' := fun h => h }
  exact (box_preconnected n ⟨x.1, mem_boxFinset.mp x.2⟩ ⟨y.1, mem_boxFinset.mp y.2⟩).map f

theorem threeExitGraph_connected (inside : Fin 3 → Site d)
    (hinside : ∀ i, inside i ∈ box d n) :
    (threeExitGraph (n := n) inside).Connected := by
  classical
  rw [connected_iff]
  refine ⟨?_, ⟨Sum.inr 0⟩⟩
  intro a b
  let core : Fin 3 → ↑(boxFinset d n) := fun i =>
    ⟨inside i, by
      simpa only [boxFinset, Set.Finite.mem_toFinset] using hinside i⟩
  have tip_core : ∀ i, (threeExitGraph inside).Adj (Sum.inr i) (Sum.inl (core i)) := by
    intro i
    simp [threeExitGraph, core]
  have toCore : ∀ z : ThreeExitVertex d n,
      ∃ q : ↑(boxFinset d n), (threeExitGraph inside).Reachable z (Sum.inl q) := by
    rintro (q | i)
    · exact ⟨q, Reachable.refl _⟩
    · exact ⟨core i, (tip_core i).reachable⟩
  obtain ⟨qa, ha⟩ := toCore a
  obtain ⟨qb, hb⟩ := toCore b
  exact ha.trans ((threeExitGraph_core_reachable inside).trans hb.symm)

def threeExitSite (outside : Fin 3 → Site d) : ThreeExitVertex d n → Site d
  | Sum.inl x => x.1
  | Sum.inr i => outside i

theorem threeExitSite_injective (outside : Fin 3 → Site d)
    (hout : ∀ i, outside i ∉ box d n) (houtinj : Function.Injective outside) :
    Function.Injective (threeExitSite (d := d) (n := n) outside) := by
  intro a b h
  rcases a with a | i <;> rcases b with b | j
  · exact congrArg Sum.inl (Subtype.ext h)
  · exfalso
    change a.1 = outside j at h
    exact hout j (h ▸ (by
      simpa only [boxFinset, Set.Finite.mem_toFinset] using a.2))
  · exfalso
    change outside i = b.1 at h
    exact hout i (h.symm ▸ (by
      simpa only [boxFinset, Set.Finite.mem_toFinset] using b.2))
  · exact congrArg Sum.inr (houtinj h)

theorem threeExitGraph_maps_to_lattice (inside outside : Fin 3 → Site d)
    (hexit : ∀ i, (hypercubicLattice d).Adj (inside i) (outside i))
    {a b : ThreeExitVertex d n} (hab : (threeExitGraph inside).Adj a b) :
    (hypercubicLattice d).Adj (threeExitSite outside a) (threeExitSite outside b) := by
  rcases a with a | i <;> rcases b with b | j
  · exact hab
  · simpa [threeExitGraph, threeExitSite] using hab ▸ hexit j
  · simpa [threeExitGraph, threeExitSite] using hab ▸ (hexit i).symm
  · simp [threeExitGraph] at hab

theorem lattice_three_exit_tree (inside outside : Fin 3 → Site d)
    (hinside : ∀ i, inside i ∈ box d n)
    (hout : ∀ i, outside i ∉ box d n)
    (houtinj : Function.Injective outside)
    (hexit : ∀ i, (hypercubicLattice d).Adj (inside i) (outside i)) :
    ∃ (C : Set (ThreeExitVertex d n)) (T : SimpleGraph C)
      (_ : DecidableRel T.Adj) (hub : C) (stem leaf : Fin 3 → C),
      T.IsTree ∧
      Function.Injective (fun z : C => threeExitSite outside z.1) ∧
      (∀ a b, T.Adj a b → (threeExitGraph inside).Adj a.1 b.1) ∧
      (∀ a b, T.Adj a b →
        (hypercubicLattice d).Adj
          (threeExitSite outside a.1) (threeExitSite outside b.1)) ∧
      Function.Injective stem ∧
      (∀ i, T.Adj hub (stem i)) ∧
      Function.Injective leaf ∧
      (∀ i, ∃ j, threeExitSite outside (leaf i).1 = outside j) ∧
      (∀ j, ∃ i, (leaf i).1 = threeExitTip j) ∧
      (∀ i, (T.deleteIncidenceSet hub).Reachable (stem i) (leaf i)) ∧
      (∀ i, T.Reachable hub (leaf i)) ∧
      (∀ i j, i ≠ j →
        ¬ (T.deleteIncidenceSet hub).Reachable (leaf i) (leaf j)) := by
  classical
  let G := threeExitGraph (n := n) inside
  have hconn : G.Connected := threeExitGraph_connected inside hinside
  have hpdeg : ∀ i, G.degree (threeExitTip i) = 1 :=
    threeExitTip_degree_one inside hinside
  obtain ⟨C, T, hTdec, hub, stem, leaf, hTree, hTG, hsteminj,
      hstemadj, hleafinj, hleafTip, hstemleaf, hreach, hcut⟩ :=
    three_pendant_vertices_have_tripod G hconn threeExitTip
      threeExitTip_injective hpdeg
  choose sigma hsigma using hleafTip
  have hsigma_inj : Function.Injective sigma := by
    intro i j hij
    apply hleafinj
    apply Subtype.ext
    rw [hsigma i, hsigma j, hij]
  have hsigma_surj : Function.Surjective sigma :=
    Finite.injective_iff_surjective.mp hsigma_inj
  have htip_surj : ∀ j, ∃ i, (leaf i).1 = threeExitTip j := by
    intro j
    obtain ⟨i, hi⟩ := hsigma_surj j
    exact ⟨i, by rw [hsigma i, hi]⟩
  refine ⟨C, T, hTdec, hub, stem, leaf, hTree, ?_, hTG, ?_, hsteminj,
    hstemadj, hleafinj, ?_, htip_surj, hstemleaf, hreach, hcut⟩
  · exact (threeExitSite_injective outside hout houtinj).comp Subtype.val_injective
  · intro a b hab
    exact threeExitGraph_maps_to_lattice inside outside hexit (hTG a b hab)
  · intro i
    exact ⟨sigma i, by rw [hsigma i]; rfl⟩

end

/-! ## The graph obtained by deleting incident edges -/

section

open Set SimpleGraph Finset
open scoped BigOperators
variable {d : ℕ}

def cutVertex {V : Type*} (G : SimpleGraph V) (x : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ≠ x ∧ b ≠ x
  symm := ⟨by rintro a b ⟨h, ha, hb⟩; exact ⟨h.symm, hb, ha⟩⟩
  loopless := ⟨fun a h => G.irrefl h.1⟩

theorem openSubgraph_removeSite_eq_cutVertex (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    openSubgraph d (removeSite x ω) = cutVertex (openSubgraph d ω) x := by
  ext a b
  simp only [openSubgraph_adj, cutVertex]
  constructor
  · rintro ⟨hadj, hopen⟩
    have hxnotin : x ∉ s(a, b) := by
      intro hx
      rw [removeSite_apply_of_mem hx] at hopen
      exact Bool.false_ne_true hopen
    rw [removeSite_apply_of_notMem hxnotin] at hopen
    refine ⟨⟨hadj, hopen⟩, ?_, ?_⟩
    · rintro rfl; exact hxnotin (Sym2.mem_mk_left a b)
    · rintro rfl; exact hxnotin (Sym2.mem_mk_right a b)
  · rintro ⟨⟨hadj, hopen⟩, hax, hbx⟩
    have hxnotin : x ∉ s(a, b) := by
      rw [Sym2.mem_iff]
      rintro (h | h)
      · exact hax h.symm
      · exact hbx h.symm
    exact ⟨hadj, by rw [removeSite_apply_of_notMem hxnotin]; exact hopen⟩

end

/-! ## Joining a finite tree to three exterior branches -/

section

open Set SimpleGraph

theorem tree_exterior_amalgam_separated
    {W V : Type*} (T : SimpleGraph W) (E U : SimpleGraph V)
    (embed : W → V) (hembed : Function.Injective embed)
    (hub : W) (leaf : Fin 3 → W)
    (hcut : ∀ i j, i ≠ j →
      ¬ (T.deleteIncidenceSet hub).Reachable (leaf i) (leaf j))
    (hEsep : ∀ i j, i ≠ j → ¬ E.Reachable (embed (leaf i)) (embed (leaf j)))
    (hEonly : ∀ z y, E.Adj (embed z) y → ∃ i, z = leaf i)
    (hUdecomp : ∀ {x y}, U.Adj x y →
      E.Adj x y ∨ ∃ a b, T.Adj a b ∧ embed a = x ∧ embed b = y) :
    ∀ i j, i ≠ j →
      ¬ (U.deleteIncidenceSet (embed hub)).Reachable
        (embed (leaf i)) (embed (leaf j)) := by
  classical
  have exterior_embedded_eq : ∀ i z,
      E.Reachable (embed (leaf i)) (embed z) → z = leaf i := by
    intro i z hr
    by_cases hz : z = leaf i
    · exact hz
    obtain ⟨w⟩ := hr.symm
    have hne : embed z ≠ embed (leaf i) := fun h => hz (hembed h)
    obtain ⟨y, hzy, q, _⟩ := w.exists_eq_cons_of_ne hne
    obtain ⟨k, rfl⟩ := hEonly z y hzy
    have hki : k = i := by
      by_contra hneki
      exact hEsep i k (Ne.symm hneki) hr
    exact congrArg leaf hki
  let R : Fin 3 → V → Prop := fun i x =>
    E.Reachable (embed (leaf i)) x ∨
      ∃ z, embed z = x ∧ (T.deleteIncidenceSet hub).Reachable (leaf i) z
  have R_start : ∀ i, R i (embed (leaf i)) := fun i =>
    Or.inl (Reachable.refl _)
  have R_step : ∀ i {x y}, R i x →
      (U.deleteIncidenceSet (embed hub)).Adj x y → R i y := by
    intro i x y hx hxy
    have hUne : x ≠ embed hub ∧ y ≠ embed hub :=
      (deleteIncidenceSet_adj.mp hxy).2
    rcases hUdecomp (deleteIncidenceSet_adj.mp hxy).1 with hE | hT
    · rcases hx with hxE | ⟨z, hz, hzreach⟩
      · exact Or.inl (hxE.trans hE.reachable)
      · subst x
        obtain ⟨k, hzk⟩ := hEonly z y hE
        subst z
        have hki : k = i := by
          by_contra hne
          exact hcut i k (Ne.symm hne) hzreach
        subst k
        exact Or.inl hE.reachable
    · obtain ⟨a, b, hab, hax, hby⟩ := hT
      subst x
      subst y
      have ha : a ≠ hub := fun h => hUne.1 (h ▸ rfl)
      have hb : b ≠ hub := fun h => hUne.2 (h ▸ rfl)
      have habCut : (T.deleteIncidenceSet hub).Adj a b :=
        deleteIncidenceSet_adj.mpr ⟨hab, ha, hb⟩
      rcases hx with hxE | ⟨z, hz, hzreach⟩
      · have hai : a = leaf i := exterior_embedded_eq i a hxE
        subst a
        exact Or.inr ⟨b, rfl, habCut.reachable⟩
      · have hza : z = a := hembed hz
        subst z
        exact Or.inr ⟨b, rfl, hzreach.trans habCut.reachable⟩
  intro i j hij hr
  obtain ⟨w⟩ := hr
  have walk_R : ∀ {x y} (q : (U.deleteIncidenceSet (embed hub)).Walk x y),
      R i x → R i y := by
    intro x y q hx
    induction q with
    | nil => exact hx
    | cons h _ ih => exact ih (R_step i hx h)
  have Rend : R i (embed (leaf j)) := by
    exact walk_R w (R_start i)
  rcases Rend with hE | ⟨z, hz, hT⟩
  · exact hEsep i j hij hE
  · have hzj : z = leaf j := hembed hz
    subst z
    exact hcut i j hij hT

end

/-! ## Producing an encounter point by a finite modification -/

section

open Set SimpleGraph Finset
variable {d : ℕ}

noncomputable def treeEdges {W : Type*} [Fintype W]
    (T : SimpleGraph W) [DecidableRel T.Adj] (f : W → Site d) :
    Finset (Sym2 (Site d)) := T.edgeFinset.image (Sym2.map f)

noncomputable def treePattern (I O : Finset (Sym2 (Site d))) :
    ConfigSpace ↥I := fun e => decide (e.1 ∈ O)

def exteriorOpenGraph (omega : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    SimpleGraph (Site d) where
  Adj x y := (openSubgraph d omega).Adj x y ∧ x ∉ box d n ∧ y ∉ box d n
  symm := ⟨by rintro x y ⟨h, hx, hy⟩; exact ⟨h.symm, hy, hx⟩⟩
  loopless := ⟨fun _ h => (openSubgraph d omega).irrefl h.1⟩

theorem exteriorOpenGraph_le (omega : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    exteriorOpenGraph omega n ≤ openSubgraph d omega := fun _ _ h => h.1

theorem exists_pattern_encounter_of_three_clusters
    (omega : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x : Fin 3 → Site d)
    (hx : ∀ i, x i ∈ box d n)
    (hinf : ∀ i, (cluster d omega (x i)).Infinite)
    (hclusters : ∀ i j, i ≠ j →
      cluster d omega (x i) ≠ cluster d omega (x j)) :
    ∃ (eta : ConfigSpace ↥(incidentBoxEdges d n)) (hub : Site d),
      IsEncounterPoint d
        (setPattern (incidentBoxEdges d n) eta omega) hub := by
  classical
  let K := boxFinset d n
  have hxK : ∀ i, x i ∈ K := fun i => by
    simpa only [K, boxFinset, Set.Finite.mem_toFinset] using hx i
  let D : (i : Fin 3) → InfiniteClusterTailData omega K (x i) := fun i =>
    infiniteClusterTailData omega (x i) (hinf i) K (hxK i)
  let inside : Fin 3 → Site d := fun i => (D i).inside
  let outside : Fin 3 → Site d := fun i => (D i).outside
  have hinside : ∀ i, inside i ∈ box d n := fun i => by
    simpa only [inside, K, boxFinset, Set.Finite.mem_toFinset] using (D i).inside_mem
  have hout : ∀ i, outside i ∉ box d n := fun i h =>
    (D i).outside_not_mem (by
      simpa only [K, boxFinset, Set.Finite.mem_toFinset] using h)
  have houtinj : Function.Injective outside := by
    intro i j hij
    by_contra hne
    have hi : outside i ∈ cluster d omega (x i) :=
      (D i).tail_subset_cluster (D i).outside_mem_tail
    have hj : outside j ∈ cluster d omega (x j) :=
      (D j).tail_subset_cluster (D j).outside_mem_tail
    rw [hij] at hi
    exact hclusters i j hne
      ((cluster_eq_of_connected hi).trans (cluster_eq_of_connected hj).symm)
  have hexit : ∀ i, (hypercubicLattice d).Adj (inside i) (outside i) :=
    fun i => (D i).exit_open.1
  obtain ⟨C, T, hTdec, hub, stem, leaf, hTree, hembedInj, hTG, hTlat,
      hstemInj, hstemAdj, hleafInj, hleafSite, htipSurj, hstemLeaf,
      hTreach, hTcut⟩ :=
    lattice_three_exit_tree inside outside hinside hout houtinj hexit
  let embed : C → Site d := fun z => threeExitSite outside z.1
  have hembed : Function.Injective embed := hembedInj
  choose sigma hsigma using hleafSite
  have hsigma_inj : Function.Injective sigma := by
    intro i j hij
    apply hleafInj
    apply hembed
    change threeExitSite outside (leaf i).1 = threeExitSite outside (leaf j).1
    rw [hsigma i, hsigma j, hij]
  let I := incidentBoxEdges d n
  let O := treeEdges T embed
  let eta := treePattern I O
  let omega' := setPattern I eta omega
  let E := exteriorOpenGraph omega n
  let U := openSubgraph d omega'
  have htreeTouch : ∀ {a b : C}, T.Adj a b → s(embed a, embed b) ∈ I := by
    intro a b hab
    apply mk_mem_incidentBoxEdges (hTlat a b hab)
    have h := hTG a b hab
    rcases ha : a.1 with qa | ia <;> rcases hb : b.1 with qb | ib
    · exact Or.inl (by simpa only [threeExitSite, boxFinset, Set.Finite.mem_toFinset] using qa.2)
    · exact Or.inl (by simpa only [threeExitSite, boxFinset, Set.Finite.mem_toFinset] using qa.2)
    · exact Or.inr (by simpa only [threeExitSite, boxFinset, Set.Finite.mem_toFinset] using qb.2)
    · simp [threeExitGraph, ha, hb] at h
  have htreeOpen : ∀ {a b : C}, T.Adj a b → U.Adj (embed a) (embed b) := by
    intro a b hab
    dsimp only [U, omega']
    rw [openSubgraph_adj]
    refine ⟨hTlat a b hab, ?_⟩
    have hI := htreeTouch hab
    rw [setPattern_of_mem eta hI]
    simp only [eta, treePattern, decide_eq_true_eq]
    unfold O treeEdges
    rw [Finset.mem_image]
    exact ⟨s(a, b), by simpa using hab, by simp⟩
  let treeHom : T →g U := {
    toFun := embed
    map_rel' := fun {_ _} h => htreeOpen h
  }
  have hE_le_U : E ≤ U := by
    intro a b hab
    have hnotI : s(a, b) ∉ I := by
      change s(a, b) ∉ incidentBoxEdges d n
      rw [mem_incidentBoxEdges]
      push Not
      intro _
      exact ⟨hab.2.1, hab.2.2⟩
    change (openSubgraph d (setPattern I eta omega)).Adj a b
    rw [openSubgraph_adj]
    refine ⟨hab.1.1, ?_⟩
    rw [setPattern_of_not_mem eta hnotI]
    exact hab.1.2
  have hEsep : ∀ i j, i ≠ j →
      ¬ E.Reachable (embed (leaf i)) (embed (leaf j)) := by
    intro i j hij hr
    have hr' := hr.mono (exteriorOpenGraph_le omega n)
    change (openSubgraph d omega).Reachable
      (threeExitSite outside (leaf i).1)
      (threeExitSite outside (leaf j).1) at hr'
    rw [hsigma i, hsigma j] at hr'
    have hi : Connected d omega (x (sigma i)) (outside (sigma i)) :=
      (D (sigma i)).tail_subset_cluster (D (sigma i)).outside_mem_tail
    have hj : Connected d omega (x (sigma j)) (outside (sigma j)) :=
      (D (sigma j)).tail_subset_cluster (D (sigma j)).outside_mem_tail
    have hconn : Connected d omega (x (sigma i)) (x (sigma j)) :=
      hi.trans (hr'.trans hj.symm)
    exact hclusters (sigma i) (sigma j) (fun h => hij (hsigma_inj h))
      (cluster_eq_of_connected hconn)
  have hEonly : ∀ z y, E.Adj (embed z) y → ∃ i, z = leaf i := by
    intro z y hzy
    rcases hz : z.1 with q | k
    · exfalso
      have hqbox : q.1 ∈ box d n := by
        simpa only [boxFinset, Set.Finite.mem_toFinset] using q.2
      have hzsite : embed z = q.1 := by simp [embed, threeExitSite, hz]
      exact hzy.2.1 (hzsite.symm ▸ hqbox)
    · obtain ⟨i, hi⟩ := htipSurj k
      exact ⟨i, Subtype.ext (hz.trans hi.symm)⟩
  have hhubCore : ∃ q : ↑(boxFinset d n), hub.1 = Sum.inl q := by
    rcases hh : hub.1 with q | j
    · exact ⟨q, rfl⟩
    · exfalso
      have hdeg := threeExitTip_degree_one inside hinside j
      rw [degree_eq_one_iff_existsUnique_adj] at hdeg
      obtain ⟨z, _hz, huniq⟩ := hdeg
      have h0 : (stem 0).1 = z := huniq (stem 0).1 (by
        simpa only [threeExitTip, hh] using hTG hub (stem 0) (hstemAdj 0))
      have h1 : (stem 1).1 = z := huniq (stem 1).1 (by
        simpa only [threeExitTip, hh] using hTG hub (stem 1) (hstemAdj 1))
      exact (by decide : (0 : Fin 3) ≠ 1)
        (hstemInj (Subtype.ext (h0.trans h1.symm)))
  obtain ⟨hubCore, hhubCore⟩ := hhubCore
  have hhubBox : embed hub ∈ box d n := by
    have hmem : hubCore.1 ∈ box d n := by
      simpa only [boxFinset, Set.Finite.mem_toFinset] using hubCore.2
    simpa only [embed, threeExitSite, hhubCore] using hmem
  have hUdecomp : ∀ {a b}, U.Adj a b →
      E.Adj a b ∨ ∃ u v, T.Adj u v ∧ embed u = a ∧ embed v = b := by
    intro a b hab
    dsimp only [U, omega'] at hab
    rw [openSubgraph_adj] at hab
    by_cases htouch : a ∈ box d n ∨ b ∈ box d n
    · right
      have hI : s(a, b) ∈ I :=
        mk_mem_incidentBoxEdges hab.1 htouch
      have hopen := hab.2
      rw [setPattern_of_mem eta hI] at hopen
      have hO : s(a, b) ∈ O := by
        simpa only [eta, treePattern, decide_eq_true_eq] using hopen
      unfold O treeEdges at hO
      rw [Finset.mem_image] at hO
      obtain ⟨e, he, heq⟩ := hO
      induction e with
      | h u v =>
          rw [SimpleGraph.mem_edgeFinset] at he
          simp only [Sym2.map_mk, Sym2.eq_iff] at heq
          rcases heq with ⟨hu, hv⟩ | ⟨hu, hv⟩
          · exact ⟨u, v, he, hu, hv⟩
          · exact ⟨v, u, he.symm, hv, hu⟩
    · left
      push Not at htouch
      have hnotI : s(a, b) ∉ I := by
        change s(a, b) ∉ incidentBoxEdges d n
        rw [mem_incidentBoxEdges]
        push Not
        intro _
        exact ⟨htouch.1, htouch.2⟩
      have hopen := hab.2
      rw [setPattern_of_not_mem eta hnotI] at hopen
      change E.Adj a b
      exact ⟨⟨hab.1, hopen⟩, htouch.1, htouch.2⟩
  have hUsep := tree_exterior_amalgam_separated T E U embed hembed hub leaf
    hTcut hEsep hEonly hUdecomp
  have hE_le_Ucut : E ≤ U.deleteIncidenceSet (embed hub) := by
    intro a b hab
    rw [deleteIncidenceSet_adj]
    refine ⟨hE_le_U hab, ?_, ?_⟩
    · intro ha
      exact hab.2.1 (ha ▸ hhubBox)
    · intro hb
      exact hab.2.2 (hb ▸ hhubBox)
  let treeCutHom : T.deleteIncidenceSet hub →g
      U.deleteIncidenceSet (embed hub) := {
    toFun := embed
    map_rel' := by
      intro a b hab
      rw [deleteIncidenceSet_adj] at hab ⊢
      refine ⟨htreeOpen hab.1, ?_, ?_⟩
      · intro ha
        exact hab.2.1 (hembed ha)
      · intro hb
        exact hab.2.2 (hembed hb)
  }
  have hstemLeafCut : ∀ i,
      (U.deleteIncidenceSet (embed hub)).Reachable
        (embed (stem i)) (embed (leaf i)) := fun i =>
    by simpa [treeCutHom] using (hstemLeaf i).map treeCutHom
  have htailE : ∀ i, ∀ z ∈ (D (sigma i)).tail,
      E.Reachable (embed (leaf i)) z := by
    intro i z hz
    have houtTail := (D (sigma i)).outside_mem_tail
    obtain ⟨ha, hb, hr⟩ :=
      (D (sigma i)).tail_connected_outside
        (outside (sigma i)) houtTail z hz
    let f : ((openSubgraph d omega).induce (K : Set (Site d))ᶜ) →g E := {
      toFun := fun q => q.1
      map_rel' := by
        intro a b hab
        refine ⟨hab, ?_, ?_⟩
        · intro ha
          apply a.2
          change a.1 ∈ K
          simpa only [K, boxFinset, Set.Finite.mem_toFinset] using ha
        · intro hb
          apply b.2
          change b.1 ∈ K
          simpa only [K, boxFinset, Set.Finite.mem_toFinset] using hb
    }
    change E.Reachable (threeExitSite outside (leaf i).1) z
    rw [hsigma i]
    exact hr.map f
  have hremove : openSubgraph d (removeSite (embed hub) omega') =
      U.deleteIncidenceSet (embed hub) := by
    rw [openSubgraph_removeSite_eq_cutVertex]
    ext a b
    simp only [cutVertex, deleteIncidenceSet_adj, U]
  have hstemInf : ∀ i,
      (cluster d (removeSite (embed hub) omega') (embed (stem i))).Infinite := by
    intro i
    apply (D (sigma i)).tail_infinite.mono
    intro z hz
    change (openSubgraph d (removeSite (embed hub) omega')).Reachable
      (embed (stem i)) z
    rw [hremove]
    exact (hstemLeafCut i).trans ((htailE i z hz).mono hE_le_Ucut)
  have hstemSep : ∀ i j, i ≠ j →
      ¬ (U.deleteIncidenceSet (embed hub)).Reachable
        (embed (stem i)) (embed (stem j)) := by
    intro i j hij hr
    exact hUsep i j hij
      ((hstemLeafCut i).symm.trans (hr.trans (hstemLeafCut j)))
  refine ⟨eta, embed hub, embed (stem 0), embed (stem 1), embed (stem 2),
    ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro h
      exact (by decide : (0 : Fin 3) ≠ 1) (hstemInj (hembed h))
    · intro h
      exact (by decide : (0 : Fin 3) ≠ 2) (hstemInj (hembed h))
    · intro h
      exact (by decide : (1 : Fin 3) ≠ 2) (hstemInj (hembed h))
  · exact ⟨htreeOpen (hstemAdj 0), htreeOpen (hstemAdj 1),
      htreeOpen (hstemAdj 2)⟩
  · exact ⟨hstemInf 0, hstemInf 1, hstemInf 2⟩
  · change
      (¬ (openSubgraph d (removeSite (embed hub) omega')).Reachable
        (embed (stem 0)) (embed (stem 1))) ∧
      (¬ (openSubgraph d (removeSite (embed hub) omega')).Reachable
        (embed (stem 0)) (embed (stem 2))) ∧
      (¬ (openSubgraph d (removeSite (embed hub) omega')).Reachable
        (embed (stem 1)) (embed (stem 2)))
    rw [hremove]
    exact ⟨hstemSep 0 1 (by decide), hstemSep 0 2 (by decide),
      hstemSep 1 2 (by decide)⟩

theorem exists_pattern_encounter_of_three_sites
    (omega : ConfigSpace (Sym2 (Site d))) (n : ℕ) (a b c : Site d)
    (ha : a ∈ box d n) (hb : b ∈ box d n) (hc : c ∈ box d n)
    (hia : (cluster d omega a).Infinite)
    (hib : (cluster d omega b).Infinite)
    (hic : (cluster d omega c).Infinite)
    (hab : cluster d omega a ≠ cluster d omega b)
    (hac : cluster d omega a ≠ cluster d omega c)
    (hbc : cluster d omega b ≠ cluster d omega c) :
    ∃ (eta : ConfigSpace ↥(incidentBoxEdges d n)) (hub : Site d),
      IsEncounterPoint d
        (setPattern (incidentBoxEdges d n) eta omega) hub := by
  let x : Fin 3 → Site d := ![a, b, c]
  apply exists_pattern_encounter_of_three_clusters omega n x
  · intro i
    fin_cases i <;> assumption
  · intro i
    fin_cases i <;> assumption
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [x, ne_comm]

end

/-! ## Positive probability of an encounter point -/

section

open Set MeasureTheory Finset
variable {d : ℕ}

theorem threeMeetBox_subset_iUnion_patterns (n : ℕ) :
    threeMeetBox d n ⊆
      ⋃ eta : ConfigSpace ↥(incidentBoxEdges d n),
        ⋃ hub : Site d,
          setPattern (incidentBoxEdges d n) eta ⁻¹'
            {omega | IsEncounterPoint d omega hub} := by
  intro omega homega
  obtain ⟨_, a, b, c, ha, hb, hc, hia, hib, hic, hab, hac, hbc⟩ := homega
  obtain ⟨eta, hub, htrif⟩ := exists_pattern_encounter_of_three_sites
    omega n a b c ha hb hc hia hib hic hab hac hbc
  exact Set.mem_iUnion.mpr ⟨eta, Set.mem_iUnion.mpr ⟨hub, htrif⟩⟩

theorem exists_encounter_pos_of_threeMeetBox
    (mu : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure mu]
    (hpattern : ∀ (I : Finset (Sym2 (Site d))) (eta : ConfigSpace ↥I),
      mu.map (setPattern I eta) ≪ mu)
    (n : ℕ) (hpos : 0 < mu (threeMeetBox d n)) :
    ∃ hub : Site d, 0 < mu {omega | IsEncounterPoint d omega hub} := by
  classical
  let I := incidentBoxEdges d n
  let B : ConfigSpace ↥I → Set (ConfigSpace (Sym2 (Site d))) := fun eta ↦
    ⋃ hub : Site d,
      setPattern I eta ⁻¹' {omega | IsEncounterPoint d omega hub}
  have hcover : threeMeetBox d n ⊆ ⋃ eta, B eta := by
    simpa only [I, B] using
      (threeMeetBox_subset_iUnion_patterns (d := d) n)
  obtain ⟨eta, heta⟩ := exists_pos_of_cover mu hcover hpos
  have hself : (⋃ hub : Site d,
      setPattern I eta ⁻¹'
        {omega | IsEncounterPoint d omega hub}) ⊆
      ⋃ hub : Site d,
        setPattern I eta ⁻¹'
          {omega | IsEncounterPoint d omega hub} := fun _ h ↦ h
  obtain ⟨hub, hpre⟩ := exists_pos_of_cover mu hself heta
  refine ⟨hub, ?_⟩
  by_contra hnot
  rw [not_lt, nonpos_iff_eq_zero] at hnot
  have hzero := hpattern I eta hnot
  rw [Measure.map_apply (measurable_setPattern I eta)
    (measurableSet_isEncounterPoint hub)] at hzero
  exact (ne_of_gt hpre) hzero

/-- If infinitely many clusters occur with positive probability, a finite pattern creates
an encounter point with positive probability under a translation-invariant law that tolerates
finite changes. -/
public theorem measure_encounter_pos_of_infinite_count
    (mu : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure mu]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
    (hpattern : ∀ (I : Finset (Sym2 (Site d))) (eta : ConfigSpace ↥I),
      mu.map (setPattern I eta) ≪ mu)
    (htop : 0 < mu {omega | numInfiniteClusters d omega = ⊤}) :
    0 < mu {omega | IsEncounterPoint d omega 0} := by
  obtain ⟨n, hn⟩ := exists_threeMeetBox_pos mu htop
  obtain ⟨hub, hhub⟩ := exists_encounter_pos_of_threeMeetBox
    mu hpattern n hn
  rwa [measure_encounter_eq_origin mu hinv hub] at hhub

end

end

end MathlibExt.Probability.Percolation.BurtonKeaneWanted

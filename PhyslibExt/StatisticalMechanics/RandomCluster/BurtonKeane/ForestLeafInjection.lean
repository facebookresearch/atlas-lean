/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Probability.Percolation.InfiniteClusterCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoundaryVolumeRatio
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SpanningTreeLeafCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HallArmEnds
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxOpenForest

/-!
# Hall's condition for injecting branch vertices into forest leaves

In a finite forest every set of branch vertices reaches at least as many leaves, so branch vertices
inject into leaves reachable from them.

## i. Overview

`fli_satSet G S` is the set of vertices reachable from `S`. In a finite forest the leaves in the
saturation of any set of degree-≥3 vertices outnumber that set (`fli_forest_leaf_hall`), so Hall's
marriage theorem gives an injection from branch vertices to leaves in their components
(`fli_branch_leaf_injection`). Applied to an open forest in a box whose leaves lie on the boundary
(`bst_BoxOpenForest`), this assigns distinct boundary arm ends to the trifurcations and bounds their
number by the boundary size.

No certificate of this kind can hold for every configuration: each one yields the
trifurcation-to-boundary injection `tfc_DistinctArmEnds`, and `tfc_not_forall_distinctArmEnds` shows
that this injection fails for some configuration in every dimension `d ≥ 1` (in `tfc_lineConfig`
every site is a trifurcation in the sense of `IsTrifurcation`). The certificate is useful
configuration by configuration; the deterministic counting bound is the reusable content.

## ii. Key results

- `fli_forest_leaf_hall` : Hall's condition: branch vertices reach at least as many leaves
- `fli_branch_leaf_injection` : an injection from branch vertices to reachable leaves
- `fli_distinctArmEnds_of_boxOpenForest` : a box open forest yields distinct boundary arm ends
- `fli_Tcount_le_boundary_of_boxOpenForest` : the trifurcation count is at most the boundary size

## iii. Table of contents

- A. Definitions
- B. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

section ForestLeaf

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## A. Definitions -/

/-- The saturation of `S` in `G`: all vertices reachable from some vertex of `S`. -/
def fli_satSet (G : SimpleGraph V) (S : Finset V) : Set V :=
  {v | ∃ x ∈ S, G.Reachable v x}

/-! ## B. Results -/

omit [Fintype V] [DecidableEq V] in
lemma fli_satSet_closed_adj (G : SimpleGraph V) {S : Finset V} {v w : V}
    (hadj : G.Adj v w) (hv : v ∈ fli_satSet G S) : w ∈ fli_satSet G S := by
  obtain ⟨x, hx, hxv⟩ := hv
  exact ⟨x, hx, (hadj.symm.reachable).trans hxv⟩

omit [Fintype V] [DecidableEq V] in
lemma fli_satSet_neighborSet_subset (G : SimpleGraph V) {S : Finset V} {v : V}
    (hv : v ∈ fli_satSet G S) : G.neighborSet v ⊆ fli_satSet G S :=
  fun _ hw => fli_satSet_closed_adj G hw hv

omit [Fintype V] [DecidableEq V] in
lemma fli_mem_satSet_of_mem (G : SimpleGraph V) {S : Finset V} {x : V} (hx : x ∈ S) :
    x ∈ fli_satSet G S := ⟨x, hx, Reachable.refl x⟩

lemma fli_forest_leaf_hall (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v)
    (S : Finset V) (hS3 : ∀ x ∈ S, 3 ≤ G.degree x) :
    S.card ≤ (S.biUnion (fun x => univ.filter
      (fun ℓ => G.degree ℓ = 1 ∧ G.Reachable x ℓ))).card := by
  classical
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · subst hSe; simp
  set s : Set V := fli_satSet G S with hs
  have : Fintype s := Set.Finite.fintype (Set.toFinite s)
  have : Nonempty s := by
    obtain ⟨x, hx⟩ := hSne
    exact ⟨⟨x, fli_mem_satSet_of_mem G hx⟩⟩
  set H : SimpleGraph s := G.induce s with hH
  have : DecidableRel H.Adj := fun a b => instDecidableComapAdj _ G a b
  have hHac : H.IsAcyclic := hacyc.of_comap _
  have hdeg : ∀ v : s, H.degree v = G.degree v.1 := by
    intro v
    have := SimpleGraph.degree_induce_of_neighborSet_subset (G := G)
      (fli_satSet_neighborSet_subset G (S := S) v.2)
    convert this using 2
  have hHmin : ∀ v : s, 1 ≤ H.degree v := fun v => by rw [hdeg v]; exact hmin v.1
  have hcount := flc2_forest_internal_le_leaves H hHac hHmin
  set branchS : Finset s := univ.filter (fun v => 3 ≤ H.degree v) with hbranchS
  set leafS : Finset s := univ.filter (fun v => H.degree v = 1) with hleafS
  set branchV : Finset V := branchS.image Subtype.val with hbranchV
  set leafV : Finset V := leafS.image Subtype.val with hleafV
  have hvalinj : Function.Injective (Subtype.val : s → V) := Subtype.val_injective
  have hbcard : branchV.card = branchS.card := Finset.card_image_of_injective branchS hvalinj
  have hlcard : leafV.card = leafS.card := Finset.card_image_of_injective leafS hvalinj
  have hSsub : S ⊆ branchV := by
    intro x hx
    rw [hbranchV, Finset.mem_image]
    refine ⟨⟨x, fli_mem_satSet_of_mem G hx⟩, ?_, rfl⟩
    rw [hbranchS, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [hdeg]; exact hS3 x hx⟩
  have hleafsub : leafV ⊆ S.biUnion (fun x => univ.filter
      (fun ℓ => G.degree ℓ = 1 ∧ G.Reachable x ℓ)) := by
    intro ℓ hℓ
    rw [hleafV, Finset.mem_image] at hℓ
    obtain ⟨v, hvleaf, rfl⟩ := hℓ
    rw [hleafS, Finset.mem_filter] at hvleaf
    have hdeg1 : G.degree v.1 = 1 := by rw [← hdeg]; exact hvleaf.2
    obtain ⟨x, hx, hreach⟩ := v.2
    rw [Finset.mem_biUnion]
    exact ⟨x, hx, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hdeg1, hreach.symm⟩⟩
  calc S.card ≤ branchV.card := Finset.card_le_card hSsub
    _ = branchS.card := hbcard
    _ ≤ leafS.card := hcount
    _ = leafV.card := hlcard.symm
    _ ≤ _ := Finset.card_le_card hleafsub

lemma fli_branch_leaf_injection (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v) (S : Finset V)
    (hS3 : ∀ x ∈ S, 3 ≤ G.degree x) :
    ∃ ψ : V → V, (∀ x ∈ S, G.degree (ψ x) = 1 ∧ G.Reachable x (ψ x)) ∧ Set.InjOn ψ S := by
  classical
  set armEnds : V → Finset V :=
    fun x => univ.filter (fun ℓ => G.degree ℓ = 1 ∧ G.Reachable x ℓ) with harm
  have hHall : ∀ T : Finset V, T ⊆ S → T.card ≤ (T.biUnion armEnds).card :=
    fun T hT => fli_forest_leaf_hall G hacyc hmin T (fun x hx => hS3 x (hT hx))
  obtain ⟨ψ, hψmem, hψinj⟩ := bhs_exists_injOn_of_hall S armEnds hHall
  refine ⟨ψ, fun x hx => ?_, hψinj⟩
  have := hψmem x hx
  rw [harm, Finset.mem_filter] at this
  exact this.2

end ForestLeaf

variable {d : ℕ}

lemma fli_reachable_to_connected {ω : ConfigSpace (Sym2 (Site d))} {Vset : Finset (Site d)}
    {F : SimpleGraph (↑Vset : Type)} [DecidableRel F.Adj]
    (hπ : ∀ u v, F.Adj u v → (openSubgraph d ω).Adj (u : Site d) (v : Site d))
    {u v : (↑Vset : Type)} (h : F.Reachable u v) :
    Connected d ω (u : Site d) (v : Site d) := by
  set f : F →g (openSubgraph d ω) :=
    { toFun := fun u => (u : Site d), map_rel' := fun {a b} hab => hπ a b hab } with hf
  exact h.map f

open Classical in
lemma fli_distinctArmEnds_of_boxOpenForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bst_BoxOpenForest ω n) : tfc_DistinctArmEnds ω n := by
  classical
  obtain ⟨Vset, hVne, F, _, vx, b, hπ, hacyc, hmin, htriData, hleaf⟩ := h
  set Tf := tfc_trifFinset ω n with hTf
  set S : Finset (↑Vset : Type) := Tf.image vx with hS
  have hvxval : ∀ x, x ∈ box d n → IsTrifurcation d ω x → (vx x : Site d) = x :=
    fun x hxbox htri => (htriData x hxbox htri).1
  have hdeg3 : ∀ x, x ∈ box d n → IsTrifurcation d ω x → 3 ≤ F.degree (vx x) := by
    intro x hxbox htri
    obtain ⟨hvx, hreach, hcut⟩ := htriData x hxbox htri
    exact bst_deg_ge_three_of_boxOpenForest hπ hxbox htri hvx hreach hcut
  have hvxinjOn : Set.InjOn vx Tf := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, tfc_mem_trifFinset] at hx hy
    rw [← hvxval x hx.1 hx.2, ← hvxval y hy.1 hy.2, hxy]
  have hS3 : ∀ w ∈ S, 3 ≤ F.degree w := by
    intro w hw
    rw [hS, Finset.mem_image] at hw
    obtain ⟨x, hxT, rfl⟩ := hw
    rw [tfc_mem_trifFinset] at hxT
    exact hdeg3 x hxT.1 hxT.2
  obtain ⟨ψ, hψmem, hψinj⟩ := fli_branch_leaf_injection F hacyc hmin S hS3
  refine ⟨fun x => (ψ (vx x) : Site d), ?_, ?_⟩
  · intro x hxbox htri
    have hxS : vx x ∈ S := by
      rw [hS, Finset.mem_image]; exact ⟨x, tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩, rfl⟩
    obtain ⟨hleaf1, hreach⟩ := hψmem (vx x) hxS
    refine ⟨hleaf (ψ (vx x)) hleaf1, ?_⟩
    have hconn : Connected d ω (vx x : Site d) (ψ (vx x) : Site d) :=
      fli_reachable_to_connected hπ hreach
    rwa [hvxval x hxbox htri] at hconn
  · intro x hxbox htri y hybox htriy hxy
    have hxS : vx x ∈ S := by
      rw [hS, Finset.mem_image]; exact ⟨x, tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩, rfl⟩
    have hyS : vx y ∈ S := by
      rw [hS, Finset.mem_image]; exact ⟨y, tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩, rfl⟩
    have hψeq : ψ (vx x) = ψ (vx y) := Subtype.val_injective hxy
    have hvxeq : vx x = vx y := hψinj hxS hyS hψeq
    rw [← hvxval x hxbox htri, ← hvxval y hybox htriy, hvxeq]

lemma fli_Tcount_le_boundary_of_boxOpenForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bst_BoxOpenForest ω n) : Tcount d ω n ≤ boxSV_boundaryCard d n :=
  tfc_Tcount_le_boundary_of_distinctArmEnds ω n (fli_distinctArmEnds_of_boxOpenForest ω n h)

lemma fli_star_injection :
    ∃ ψ : Fin 4 → Fin 4,
      (∀ x ∈ ({0} : Finset (Fin 4)), Flc2Witness.starG.degree (ψ x) = 1 ∧
        Flc2Witness.starG.Reachable x (ψ x)) ∧ Set.InjOn ψ ({0} : Finset (Fin 4)) := by
  apply fli_branch_leaf_injection Flc2Witness.starG Flc2Witness.starG_isTree.isAcyclic
  · intro v; fin_cases v <;> decide
  · intro x hx
    simp only [Finset.mem_singleton] at hx; subst hx
    rw [Flc2Witness.starG_centre_deg]

lemma fli_star_hall :
    ({0} : Finset (Fin 4)).card ≤
      (({0} : Finset (Fin 4)).biUnion (fun x => univ.filter
        (fun ℓ => Flc2Witness.starG.degree ℓ = 1 ∧ Flc2Witness.starG.Reachable x ℓ))).card := by
  apply fli_forest_leaf_hall Flc2Witness.starG Flc2Witness.starG_isTree.isAcyclic
  · intro v; fin_cases v <;> decide
  · intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
    rw [Flc2Witness.starG_centre_deg]

lemma fli_path_injection :
    ∃ ψ : Fin 2 → Fin 2,
      (∀ x ∈ (∅ : Finset (Fin 2)), Flc2Witness.pathG.degree (ψ x) = 1 ∧
        Flc2Witness.pathG.Reachable x (ψ x)) ∧ Set.InjOn ψ (∅ : Finset (Fin 2)) := by
  apply fli_branch_leaf_injection Flc2Witness.pathG Flc2Witness.pathG_isTree.isAcyclic
  · intro v; rw [Flc2Witness.pathG_deg]
  · intro x hx; simp at hx

end Percolation

end StatMech

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Probability.Percolation.InfiniteClusterCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndDisjoint
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestLeafSelection
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TwoFoldForestArms

/-!
# Two-fold arm covers and claw configurations

A claw of four trifurcations with six arm colours cannot carry a two-fold forest arm cover, while
two-fold forest arms give leaf selections.

## i. Overview

`tffa_ValidBranch ω n u` says that `u` stays in an infinite cluster after all trifurcations are
removed. `tffa_TwoFoldClawConfig` describes a claw: a trifurcation joined to three others, with
branches coloured by six colours. Counting shows such a claw excludes two-fold forest arms
(`tffa_count_unsat`). Conversely, two-fold forest arms give a leaf selection and hence the
spanning-tree certificate.

## ii. Key results

- `tffa_count_unsat` : the counting obstruction for the claw
- `tffa_claw_excludes_twoFoldForestArms` : a claw configuration excludes two-fold forest arms
- `tffa_leafDisjoint_of_twoFoldForestArms` : two-fold forest arms give a leaf selection

## iii. Table of contents

- A. Results

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

variable {d : ℕ}

/-! ## A. Results -/

lemma tffa_count_unsat (f : Option (Fin 4 × Fin 2) → Fin 6) (hf : Function.Injective f) :
    False := by
  have h := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin] at h
  omega


open Classical in
/-- `u` lies in an infinite cluster after all trifurcations of `B_n` are removed. -/
def tffa_ValidBranch (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (u : Site d) : Prop :=
  (cluster d (removeSites (tfc_trifFinset ω n) ω) u).Infinite


open Classical in
/-- A claw configuration in `B_n`: a trifurcation `x₀`, three further trifurcations `y i`, no
others, and a six-colouring of valid branches compatible with connectivity. -/
def tffa_TwoFoldClawConfig (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (x₀ : Site d) (y : Fin 3 → Site d) (κ : Site d → Fin 6),
    (x₀ ∈ box d n ∧ IsTrifurcation d ω x₀) ∧
    (∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i) ∧
    Function.Injective y ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i) ∧
    (∀ u v, tffa_ValidBranch ω n u → tffa_ValidBranch ω n v →
      κ u = κ v → aed_sameGlobalComponent (tfc_trifFinset ω n) ω u v)


open Classical in
lemma tffa_not_twoFoldForestArms_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hclaw : tffa_TwoFoldClawConfig ω n) :
    ¬ tfh_TwoFoldForestArms ω n := by
  classical
  obtain ⟨x₀, y, κ, ⟨hx0box, htri0⟩, hydata, hyinj, hexhaust, hκ⟩ := hclaw
  rintro ⟨r, b, ⟨hrbox, hrinf⟩, hexist, hrootSep, hbranchSep⟩
  set tl : Fin 4 → Site d := fun k => if h : k = 0 then x₀ else y (k.pred h) with htl
  have htlbox : ∀ k, tl k ∈ box d n := by
    intro k; simp only [htl]
    by_cases hk : k = 0
    · rw [dite_eq_left hk]; exact hx0box
    · rw [dite_eq_right hk]; exact (hydata _).1
  have htltri : ∀ k, IsTrifurcation d ω (tl k) := by
    intro k; simp only [htl]
    by_cases hk : k = 0
    · rw [dite_eq_left hk]; exact htri0
    · rw [dite_eq_right hk]; exact (hydata _).2.1
  have htlinj : Function.Injective tl := by
    intro a c hac
    simp only [htl] at hac
    by_cases ha : a = 0 <;> by_cases hc : c = 0
    · rw [ha, hc]
    · rw [dite_eq_left ha, dite_eq_right hc] at hac; exact absurd hac (hydata _).2.2
    · rw [dite_eq_right ha, dite_eq_left hc] at hac; exact absurd hac.symm (hydata _).2.2
    · rw [dite_eq_right ha, dite_eq_right hc] at hac; exact Fin.pred_inj.mp (hyinj hac)
  set sidx : Option (Fin 4 × Fin 2) → Site d :=
    fun p => p.elim r (fun q => b (tl q.1) q.2) with hsidx
  have hvalid : ∀ p, tffa_ValidBranch ω n (sidx p) := by
    intro p
    cases p with
    | none => exact hrinf
    | some q =>
        obtain ⟨_, _, hbinf⟩ := hexist (tl q.1) (htlbox q.1) (htltri q.1) q.2
        exact hbinf
  set κidx : Option (Fin 4 × Fin 2) → Fin 6 := fun p => κ (sidx p) with hκidx
  have hsep : ∀ p q : Option (Fin 4 × Fin 2), p ≠ q →
      ¬ aed_sameGlobalComponent (tfc_trifFinset ω n) ω (sidx p) (sidx q) := by
    intro p q hpq
    cases p with
    | none =>
      cases q with
      | none => exact absurd rfl hpq
      | some q' =>
          exact hrootSep (tl q'.1) (htlbox q'.1) (htltri q'.1) q'.2
    | some p' =>
      cases q with
      | none =>
          intro hc
          exact hrootSep (tl p'.1) (htlbox p'.1) (htltri p'.1) p'.2 hc.symm
      | some q' =>
          have hne' : (tl p'.1, p'.2) ≠ (tl q'.1, q'.2) := by
            intro hcontra
            rw [Prod.mk.injEq] at hcontra
            apply hpq
            have h1 : p'.1 = q'.1 := htlinj hcontra.1
            exact congrArg some (Prod.ext h1 hcontra.2)
          exact hbranchSep (tl p'.1) (htlbox p'.1) (htltri p'.1) p'.2
            (tl q'.1) (htlbox q'.1) (htltri q'.1) q'.2 hne'
  have hκidxinj : Function.Injective κidx := by
    intro p q hpq
    by_contra hne'
    exact hsep p q hne' (hκ (sidx p) (sidx q) (hvalid p) (hvalid q) hpq)
  exact tffa_count_unsat κidx hκidxinj

lemma tffa_claw_excludes_twoFoldForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hclaw : tffa_TwoFoldClawConfig ω n) (h : tfh_TwoFoldForestArms ω n) : False :=
  tffa_not_twoFoldForestArms_of_claw ω n hclaw h


open Classical in
lemma tffa_claw_coloring_consistent (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    (_n : ℕ) (rep : Fin 6 → Site d)
    (hcover : ∀ u, (cluster d (removeSites T ω) u).Infinite →
      ∃ i, Connected d (removeSites T ω) (rep i) u) :
    ∃ κ : Site d → Fin 6, ∀ u v, (cluster d (removeSites T ω) u).Infinite →
      (cluster d (removeSites T ω) v).Infinite → κ u = κ v →
      aed_sameGlobalComponent T ω u v := by
  classical
  set R := Connected d (removeSites T ω) with hR
  have hRequiv : Equivalence R := aed_globalCut_equiv T ω
  refine ⟨fun u => if h : ∃ i, R (rep i) u then h.choose else 0, ?_⟩
  intro u v hu hv huv
  simp only at huv
  have heu : ∃ i, R (rep i) u := hcover u hu
  have hev : ∃ i, R (rep i) v := hcover v hv
  rw [dite_eq_left heu, dite_eq_left hev] at huv
  have h1 : R (rep heu.choose) u := heu.choose_spec
  have h2 : R (rep hev.choose) v := hev.choose_spec
  rw [huv] at h1
  exact hRequiv.trans (hRequiv.symm h1) h2


open Classical in
lemma tffa_twoFoldClawConfig_of_sixArmCover (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ : Site d} {y : Fin 3 → Site d}
    (hx0 : x₀ ∈ box d n ∧ IsTrifurcation d ω x₀)
    (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i)
    (hyinj : Function.Injective y)
    (hexhaust : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
    (rep : Fin 6 → Site d)
    (hcover : ∀ u, (cluster d (removeSites (tfc_trifFinset ω n) ω) u).Infinite →
      ∃ i, Connected d (removeSites (tfc_trifFinset ω n) ω) (rep i) u) :
    tffa_TwoFoldClawConfig ω n := by
  obtain ⟨κ, hκ⟩ := tffa_claw_coloring_consistent (tfc_trifFinset ω n) ω n rep hcover
  exact ⟨x₀, y, κ, hx0, hydata, hyinj, hexhaust, fun u v hu hv huv => hκ u v hu hv huv⟩

/-- The leaf selection `str_ForestLeafSelection`. -/
def tffa_LeafDisjointSelection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  str_ForestLeafSelection ω n

lemma tffa_spanningTreeLeafCount_of_leafDisjoint (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : tffa_LeafDisjointSelection ω n)
    (hbase : (∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) → flc2_SpanningTreeLeafCount ω n) :
    flc2_SpanningTreeLeafCount ω n :=
  str_spanningTreeLeafCount_of_forestLeafSelection ω n h hbase

lemma tffa_leafDisjoint_of_twoFoldForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : tfh_TwoFoldForestArms ω n) :
    tffa_LeafDisjointSelection ω n :=
  tfh_forestLeafSelection_of_twoFoldForestArms ω n hn h

end Percolation

end StatMech

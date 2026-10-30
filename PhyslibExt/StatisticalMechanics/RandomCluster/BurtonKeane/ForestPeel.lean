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
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneMerge
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndsDistinct
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestLeafInjectionBound
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SingleCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateArmTwoTrif

/-!
# Coherent arm selectors and forest peeling

Choosing for each trifurcation an infinite arm not occupied by any other trifurcation gives
single-cut branch separation and the Burton–Keane trifurcation count.

## i. Overview

Removing a trifurcation `x` splits its cluster into arms; `bkfl_inArm` records which arm a site lies
in. A coherent arm selector picks an arm site for every trifurcation so that every other connected
trifurcation lies outside that arm (`bkfl_PrivateFar`). Forest peeling (`bkfl_ForestPeel`) asks
instead for an arm free of other trifurcations that every other trifurcation can still reach. Each
version yields single-cut branch separation and so `Tcount ≤ |∂B_n|`. The certificate holds when
there are at most two trifurcations or when the trifurcations lie in distinct clusters.

No certificate of this kind can hold for every configuration: each one yields the
trifurcation-to-boundary injection `tfc_DistinctArmEnds`, and `tfc_not_forall_distinctArmEnds` shows
that this injection fails for some configuration in every dimension `d ≥ 1` (in `tfc_lineConfig`
every site is a trifurcation in the sense of `IsTrifurcation`). The certificate is useful
configuration by configuration; the deterministic counting bound is the reusable content.

## ii. Key results

- `bkfl_arms_separate` : distinct arms of a trifurcation are disconnected after its removal
- `bkfl_Tcount_le_boundary_of_coherentSelector` : the counting bound from a coherent selector
- `bkfl_existsPrivateArm_of_forestPeel` : forest peeling gives a private arm for each trifurcation
- `bkfl_Tcount_le_boundary_of_forestPeel` : the counting bound from forest peeling
- `bkfl_forestPeel_of_twoTrif` : forest peeling with two trifurcations

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

variable {d : ℕ}

/-! ## A. Definitions -/

/-- `v` lies in the arm of the trifurcation `x` containing `a`: `a` and `v` are connected after `x`
is removed. -/
def bkfl_inArm (ω : ConfigSpace (Sym2 (Site d))) (x a v : Site d) : Prop :=
  Connected d (removeSite x ω) a v

/-! ## B. Results -/

lemma bkfl_inArm_self (ω : ConfigSpace (Sym2 (Site d))) (x a : Site d) :
    bkfl_inArm ω x a a := connected_rfl

lemma bkfl_inArm_symm_witness (ω : ConfigSpace (Sym2 (Site d))) {x a a' v : Site d}
    (haa' : Connected d (removeSite x ω) a a') (h : bkfl_inArm ω x a v) :
    bkfl_inArm ω x a' v := haa'.symm.trans h

lemma bkfl_sameArm_connected (ω : ConfigSpace (Sym2 (Site d))) {x a u v : Site d}
    (hu : bkfl_inArm ω x a u) (hv : bkfl_inArm ω x a v) :
    Connected d (removeSite x ω) u v := hu.symm.trans hv

lemma bkfl_arms_separate (ω : ConfigSpace (Sym2 (Site d))) {x a b u w : Site d}
    (hdis : ¬ Connected d (removeSite x ω) a b)
    (hu : bkfl_inArm ω x a u) (hw : bkfl_inArm ω x b w) :
    ¬ Connected d (removeSite x ω) u w := by
  intro huw
  exact hdis (hu.trans (huw.trans hw.symm))

lemma bkfl_atMostOneArm (ω : ConfigSpace (Sym2 (Site d))) {x a₁ a₂ a₃ v : Site d}
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) :
    ¬ (bkfl_inArm ω x a₁ v ∧ bkfl_inArm ω x a₂ v) ∧
    ¬ (bkfl_inArm ω x a₁ v ∧ bkfl_inArm ω x a₃ v) ∧
    ¬ (bkfl_inArm ω x a₂ v ∧ bkfl_inArm ω x a₃ v) :=
  ⟨fun ⟨h1, h2⟩ => bkfl_arms_separate ω hd12 h1 h2 connected_rfl,
   fun ⟨h1, h3⟩ => bkfl_arms_separate ω hd13 h1 h3 connected_rfl,
   fun ⟨h2, h3⟩ => bkfl_arms_separate ω hd23 h2 h3 connected_rfl⟩

/-- The arm selected for `x` avoids `y`, while the arm selected for `y` reaches `y` after `x` is
removed. -/
def bkfl_PrivateFar (ω : ConfigSpace (Sym2 (Site d))) (b : Site d → Site d)
    (x y : Site d) : Prop :=
  ¬ bkfl_inArm ω x (b x) y ∧ Connected d (removeSite x ω) (b y) y

lemma bkfl_singleCut_sep_of_privateFar (ω : ConfigSpace (Sym2 (Site d)))
    (b : Site d → Site d) {x y : Site d} (h : bkfl_PrivateFar ω b x y) :
    ¬ Connected d (removeSite x ω) (b x) (b y) := by
  obtain ⟨hpriv, hfar⟩ := h
  intro hbxby
  exact hpriv (hbxby.trans hfar)

/-- The selected arm site `b x` lies in the box, is connected to `x`, and its cluster stays infinite
after all trifurcations of the box are removed. -/
def bkfl_ArmData (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (b : Site d → Site d)
    (x : Site d) : Prop :=
  b x ∈ box d n ∧ Connected d ω x (b x) ∧
    (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite

/-- A coherent arm selector for `B_n`: arm data for every trifurcation, private with respect to
every other connected trifurcation. -/
def bkfl_CoherentArmSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → bkfl_ArmData ω n b x) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → bkfl_PrivateFar ω b x y)

lemma bkfl_privateArm_of_coherentSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bkfl_CoherentArmSelector ω n) : daepf_PrivateArm ω n := by
  obtain ⟨b, hdata, hpair⟩ := h
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    exact hdata x hxbox htri
  · intro x hxbox htri y hybox htriy hxy hconn
    obtain ⟨hpriv, hfar⟩ := hpair x hxbox htri y hybox htriy hxy hconn
    exact ⟨hpriv, hfar⟩

lemma bkfl_singleCutBranchSeparation_of_coherentSelector
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (h : bkfl_CoherentArmSelector ω n) :
    daep2_SingleCutBranchSeparation ω n :=
  daepf_singleCutBranchSeparation_of_privateArm ω n
    (bkfl_privateArm_of_coherentSelector ω n h)

lemma bkfl_Tcount_le_boundary_of_coherentSelector (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hn : 1 ≤ n) (h : bkfl_CoherentArmSelector ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  daepf_Tcount_le_boundary_of_privateArm ω n hn
    (bkfl_privateArm_of_coherentSelector ω n h)

/-- Pointwise private arm at `x` with respect to the set `T`: the arm site `bx` avoids every other
element of `T` after `x` is removed, and stays connected to `x` after any other element is
removed. -/
def bkfl_PointwisePrivateFar (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (T : Finset (Site d)) (x bx : Site d) : Prop :=
  (bx ∈ box d n ∧ Connected d ω x bx ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) bx).Infinite) ∧
    (∀ y ∈ T, y ≠ x → ¬ Connected d (removeSite x ω) bx y) ∧
    (∀ z ∈ T, z ≠ x → Connected d (removeSite z ω) bx x)

/-- Every trifurcation of `B_n` has a pointwise private arm with respect to all trifurcations. -/
def bkfl_ExistsPrivateArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∀ x, x ∈ box d n → IsTrifurcation d ω x →
    ∃ bx, bkfl_PointwisePrivateFar ω n (tfc_trifFinset ω n) x bx

lemma bkfl_coherentSelector_of_existsPrivateArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bkfl_ExistsPrivateArm ω n) : bkfl_CoherentArmSelector ω n := by
  classical
  set b : Site d → Site d := fun x =>
    if hx : x ∈ box d n ∧ IsTrifurcation d ω x then (h x hx.1 hx.2).choose else x with hb
  have hbval : ∀ x (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x),
      b x = (h x hxbox htri).choose := by
    intro x hxbox htri
    simp only [hb, dite_eq_left (⟨hxbox, htri⟩ : x ∈ box d n ∧ IsTrifurcation d ω x)]
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    have hspec := (h x hxbox htri).choose_spec
    rw [bkfl_ArmData, hbval x hxbox htri]
    exact hspec.1
  · intro x hxbox htri y hybox htriy hxy hconn
    have hspecx := (h x hxbox htri).choose_spec
    have hspecy := (h y hybox htriy).choose_spec
    have hyT : y ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
    have hxT : x ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
    refine ⟨?_, ?_⟩
    · rw [bkfl_inArm, hbval x hxbox htri]
      exact hspecx.2.1 y hyT (Ne.symm hxy)
    · rw [hbval y hybox htriy]
      exact hspecy.2.2 x hxT hxy

lemma bkfl_privateArm_of_existsPrivateArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bkfl_ExistsPrivateArm ω n) : daepf_PrivateArm ω n :=
  bkfl_privateArm_of_coherentSelector ω n (bkfl_coherentSelector_of_existsPrivateArm ω n h)

lemma bkfl_Tcount_le_boundary_of_existsPrivateArm (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hn : 1 ≤ n) (h : bkfl_ExistsPrivateArm ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bkfl_Tcount_le_boundary_of_coherentSelector ω n hn
    (bkfl_coherentSelector_of_existsPrivateArm ω n h)

lemma bkfl_trif_branches (ω : ConfigSpace (Sym2 (Site d))) {x : Site d}
    (htri : IsTrifurcation d ω x) :
    ∃ a₁ a₂ a₃ : Site d,
      (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
      (Connected d ω x a₁ ∧ Connected d ω x a₂ ∧ Connected d ω x a₃) ∧
      (¬ Connected d (removeSite x ω) a₁ a₂ ∧ ¬ Connected d (removeSite x ω) a₁ a₃ ∧
        ¬ Connected d (removeSite x ω) a₂ a₃) := by
  obtain ⟨a₁, a₂, a₃, hne, hconn, _, hsep⟩ := htri
  exact ⟨a₁, a₂, a₃, hne, hconn, hsep⟩

lemma bkfl_vertex_meets_atMostOne_arm (ω : ConfigSpace (Sym2 (Site d)))
    {x a₁ a₂ a₃ v : Site d}
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) :
    (bkfl_inArm ω x a₁ v → ¬ bkfl_inArm ω x a₂ v ∧ ¬ bkfl_inArm ω x a₃ v) ∧
    (bkfl_inArm ω x a₂ v → ¬ bkfl_inArm ω x a₁ v ∧ ¬ bkfl_inArm ω x a₃ v) ∧
    (bkfl_inArm ω x a₃ v → ¬ bkfl_inArm ω x a₁ v ∧ ¬ bkfl_inArm ω x a₂ v) := by
  obtain ⟨n12, n13, n23⟩ := bkfl_atMostOneArm ω hd12 hd13 hd23 (v := v)
  exact ⟨fun h1 => ⟨fun h2 => n12 ⟨h1, h2⟩, fun h3 => n13 ⟨h1, h3⟩⟩,
    fun h2 => ⟨fun h1 => n12 ⟨h1, h2⟩, fun h3 => n23 ⟨h2, h3⟩⟩,
    fun h3 => ⟨fun h1 => n13 ⟨h1, h3⟩, fun h2 => n23 ⟨h2, h3⟩⟩⟩

lemma bkfl_pointwise_of_freeArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (T : Finset (Site d)) {x a : Site d}
    (hdata : a ∈ box d n ∧ Connected d ω x a ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) a).Infinite)
    (hfree : ∀ y ∈ T, y ≠ x → ¬ Connected d (removeSite x ω) a y)
    (hfar : ∀ z ∈ T, z ≠ x → Connected d (removeSite z ω) a x) :
    bkfl_PointwisePrivateFar ω n T x a :=
  ⟨hdata, hfree, hfar⟩

/-- The arm of `x` through `a` contains another element of `T`. -/
def bkfl_Occupied (ω : ConfigSpace (Sym2 (Site d))) (T : Finset (Site d)) (x a : Site d) :
    Prop := ∃ y ∈ T, y ≠ x ∧ Connected d (removeSite x ω) a y

lemma bkfl_free_of_unoccupied (ω : ConfigSpace (Sym2 (Site d))) (T : Finset (Site d))
    {x a : Site d} (h : ¬ bkfl_Occupied ω T x a) :
    ∀ y ∈ T, y ≠ x → ¬ Connected d (removeSite x ω) a y := by
  intro y hyT hyx hc
  exact h ⟨y, hyT, hyx, hc⟩

lemma bkfl_pointwise_of_unoccupiedArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (T : Finset (Site d)) {x a : Site d}
    (hdata : a ∈ box d n ∧ Connected d ω x a ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) a).Infinite)
    (hunocc : ¬ bkfl_Occupied ω T x a)
    (hfar : ∀ z ∈ T, z ≠ x → Connected d (removeSite z ω) a x) :
    bkfl_PointwisePrivateFar ω n T x a :=
  ⟨hdata, bkfl_free_of_unoccupied ω T hunocc, hfar⟩

lemma bkfl_exists_unoccupied_arm (ω : ConfigSpace (Sym2 (Site d))) (T : Finset (Site d))
    {x a₁ a₂ a₃ : Site d}
    (hsome : ¬ bkfl_Occupied ω T x a₁ ∨ ¬ bkfl_Occupied ω T x a₂ ∨
      ¬ bkfl_Occupied ω T x a₃) :
    ∃ a ∈ ({a₁, a₂, a₃} : Finset (Site d)), ¬ bkfl_Occupied ω T x a := by
  classical
  rcases hsome with h1 | h2 | h3
  · exact ⟨a₁, by simp, h1⟩
  · exact ⟨a₂, by simp, h2⟩
  · exact ⟨a₃, by simp, h3⟩

lemma bkfl_sameArm_occupants_connected (ω : ConfigSpace (Sym2 (Site d)))
    {x a y y' : Site d}
    (hy : Connected d (removeSite x ω) a y) (hy' : Connected d (removeSite x ω) a y') :
    Connected d (removeSite x ω) y y' := hy.symm.trans hy'

/-- Forest peeling for `B_n`: every trifurcation has an unoccupied infinite arm that stays connected
to it after any other trifurcation is removed. -/
def bkfl_ForestPeel (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∀ x, x ∈ box d n → IsTrifurcation d ω x →
    ∃ a, (a ∈ box d n ∧ Connected d ω x a ∧
        (cluster d (removeSites (tfc_trifFinset ω n) ω) a).Infinite) ∧
      ¬ bkfl_Occupied ω (tfc_trifFinset ω n) x a ∧
      (∀ z ∈ tfc_trifFinset ω n, z ≠ x → Connected d (removeSite z ω) a x)

lemma bkfl_existsPrivateArm_of_forestPeel (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bkfl_ForestPeel ω n) : bkfl_ExistsPrivateArm ω n := by
  intro x hxbox htri
  obtain ⟨a, hdata, hunocc, hfar⟩ := h x hxbox htri
  exact ⟨a, bkfl_pointwise_of_unoccupiedArm ω n (tfc_trifFinset ω n) hdata hunocc hfar⟩

lemma bkfl_privateArm_of_forestPeel (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bkfl_ForestPeel ω n) : daepf_PrivateArm ω n :=
  bkfl_privateArm_of_existsPrivateArm ω n (bkfl_existsPrivateArm_of_forestPeel ω n h)

lemma bkfl_Tcount_le_boundary_of_forestPeel (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : bkfl_ForestPeel ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bkfl_Tcount_le_boundary_of_existsPrivateArm ω n hn
    (bkfl_existsPrivateArm_of_forestPeel ω n h)

lemma bkfl_forestPeel_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bkfl_ForestPeel ω n := by
  intro x hxbox htri
  exact absurd htri (hno x hxbox)

lemma bkfl_forestPeel_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    bkfl_ForestPeel ω n := by
  classical
  have hT : tfc_trifFinset ω n = {x₀} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨tfc_mem_trifFinset.mpr ⟨hx0box, htri0⟩, ?_⟩
    intro y hy; rw [tfc_mem_trifFinset] at hy; exact huniq y hy.1 hy.2
  have hcut : removeSites (tfc_trifFinset ω n) ω = removeSite x₀ ω := by
    rw [hT, daep_removeSites_singleton]
  intro x hxbox htri
  have hx0 : x = x₀ := huniq x hxbox htri
  subst hx0
  refine ⟨a, ⟨habox, haconn, ?_⟩, ?_, ?_⟩
  · rw [hcut]; exact hainf
  · rintro ⟨y, hyT, hyx, _⟩
    rw [hT, Finset.mem_singleton] at hyT
    exact hyx hyT
  · intro z hzT hzx
    rw [hT, Finset.mem_singleton] at hzT
    exact absurd hzT hzx

lemma bkfl_forestPeel_of_distinctClusters (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (arm : Site d → Site d)
    (hdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      arm x ∈ box d n ∧ Connected d ω x (arm x) ∧
        (cluster d (removeSites (tfc_trifFinset ω n) ω) (arm x)).Infinite)
    (hfar : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ z ∈ tfc_trifFinset ω n, z ≠ x → Connected d (removeSite z ω) (arm x) x)
    (hsep : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
      IsTrifurcation d ω y → x ≠ y → ¬ Connected d ω x y) :
    bkfl_ForestPeel ω n := by
  intro x hxbox htri
  refine ⟨arm x, hdata x hxbox htri, ?_, hfar x hxbox htri⟩
  rintro ⟨y, hyT, hyx, hcy⟩
  rw [tfc_mem_trifFinset] at hyT
  have hxa : Connected d ω x (arm x) := (hdata x hxbox htri).2.1
  have hay : Connected d ω (arm x) y := connected_mono (by
    intro e; unfold removeSite; by_cases h : x ∈ e
    · rw [ite_eq_left h]; exact Bool.false_le _
    · rw [ite_eq_right h]) hcy
  exact hsep x hxbox htri y hyT.1 hyT.2 (Ne.symm hyx) (hxa.trans hay)

lemma bkfl_forestPeel_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (arm : Site d → Site d)
    (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hdata_x : arm x₀ ∈ box d n ∧ Connected d ω x₀ (arm x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (arm x₀)).Infinite)
    (hdata_y : arm y₀ ∈ box d n ∧ Connected d ω y₀ (arm y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (arm y₀)).Infinite)
    (hocc_x : ¬ Connected d (removeSite x₀ ω) (arm x₀) y₀)
    (hocc_y : ¬ Connected d (removeSite y₀ ω) (arm y₀) x₀)
    (hfar_x : Connected d (removeSite y₀ ω) (arm x₀) x₀)
    (hfar_y : Connected d (removeSite x₀ ω) (arm y₀) y₀) :
    bkfl_ForestPeel ω n := by
  classical
  intro x hxbox htri
  rcases htwo x hxbox htri with rfl | rfl
  · refine ⟨arm x, hdata_x, ?_, ?_⟩
    · rintro ⟨w, hwT, hwx, hcw⟩
      rw [tfc_mem_trifFinset] at hwT
      rcases htwo w hwT.1 hwT.2 with rfl | rfl
      · exact hwx rfl
      · exact hocc_x hcw
    · intro z hzT hzx
      rw [tfc_mem_trifFinset] at hzT
      rcases htwo z hzT.1 hzT.2 with rfl | rfl
      · exact absurd rfl hzx
      · exact hfar_x
  · refine ⟨arm x, hdata_y, ?_, ?_⟩
    · rintro ⟨w, hwT, hwy, hcw⟩
      rw [tfc_mem_trifFinset] at hwT
      rcases htwo w hwT.1 hwT.2 with rfl | rfl
      · exact hocc_y hcw
      · exact hwy rfl
    · intro z hzT hzy
      rw [tfc_mem_trifFinset] at hzT
      rcases htwo z hzT.1 hzT.2 with rfl | rfl
      · exact hfar_y
      · exact absurd rfl hzy

end Percolation

end StatMech

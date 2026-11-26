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
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneMerge
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndsDistinct
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestLeafInjectionBound
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SingleCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateArmTwoTrif
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPeel
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HallArmEnds
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClawDivergentArmOrder
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndDisjoint

/-!
# Outward arms

An outward arm for each trifurcation, unoccupied by the others and reachable from them, is the same
as forest peeling and gives the trifurcation count.

## i. Overview

`fld_OutwardArm ω n` asks for each trifurcation `x` an arm site whose cluster stays infinite after
all trifurcations are removed, which no other trifurcation can reach once `x` is removed, and which
every other trifurcation reaches. This is equivalent to `bkfl_ForestPeel`; it gives global forest
arms, disjoint arm ends and `Tcount ≤ |∂B_n|`. It holds with at most two trifurcations and when the
trifurcations lie in distinct clusters.

No certificate of this kind can hold for every configuration: each one yields the
trifurcation-to-boundary injection `tfc_DistinctArmEnds`, and `tfc_not_forall_distinctArmEnds` shows
that this injection fails for some configuration in every dimension `d ≥ 1` (in `tfc_lineConfig`
every site is a trifurcation in the sense of `IsTrifurcation`). The certificate is useful
configuration by configuration; the deterministic counting bound is the reusable content.

## ii. Key results

- `fld_outwardArm_iff_forestPeel` : outward arms are forest peeling
- `fld_Tcount_le_boundary_of_outwardArm` : the counting bound
- `fld_outwardArm_of_twoTrif` : outward arms with two trifurcations

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

lemma fld_separate_of_outward_far (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x y a a' : Site d}
    (hxT : x ∈ tfc_trifFinset ω n) (hyT : y ∈ tfc_trifFinset ω n) (hxy : x ≠ y)
    (haout : ∀ z ∈ tfc_trifFinset ω n, z ≠ x → ¬ Connected d (removeSite x ω) a z)
    (hfar : Connected d (removeSite x ω) a' y) :
    ¬ Connected d (removeSites (tfc_trifFinset ω n) ω) a a' := by
  intro haa'
  have haa'_single : Connected d (removeSite x ω) a a' :=
    connected_mono (daep2_removeSites_le_removeSite (tfc_trifFinset ω n) ω hxT) haa'
  exact haout y hyT (Ne.symm hxy) (haa'_single.trans hfar)

/-- Outward arms for `B_n`: each trifurcation has an arm site whose cluster stays infinite after all
trifurcations are removed, unreachable from the other trifurcations once it is removed, and
reachable by each other trifurcation when that one is removed. -/
def fld_OutwardArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∀ x, x ∈ box d n → IsTrifurcation d ω x →
    ∃ a, (a ∈ box d n ∧ Connected d ω x a ∧
        (cluster d (removeSites (tfc_trifFinset ω n) ω) a).Infinite) ∧
      (∀ y ∈ tfc_trifFinset ω n, y ≠ x → ¬ Connected d (removeSite x ω) a y) ∧
      (∀ z ∈ tfc_trifFinset ω n, z ≠ x → Connected d (removeSite z ω) a x)

lemma fld_outwardArm_of_forestPeel (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bkfl_ForestPeel ω n) : fld_OutwardArm ω n := by
  intro x hxbox htri
  obtain ⟨a, hdata, hunocc, hfar⟩ := h x hxbox htri
  exact ⟨a, hdata, bkfl_free_of_unoccupied ω (tfc_trifFinset ω n) hunocc, hfar⟩

lemma fld_forestPeel_of_outwardArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : fld_OutwardArm ω n) : bkfl_ForestPeel ω n := by
  intro x hxbox htri
  obtain ⟨a, hdata, hout, hfar⟩ := h x hxbox htri
  refine ⟨a, hdata, ?_, hfar⟩
  rintro ⟨y, hyT, hyx, hcy⟩
  exact hout y hyT hyx hcy

lemma fld_outwardArm_iff_forestPeel (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    fld_OutwardArm ω n ↔ bkfl_ForestPeel ω n :=
  ⟨fld_forestPeel_of_outwardArm ω n, fld_outwardArm_of_forestPeel ω n⟩

lemma fld_globalForestArms_of_outwardArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : fld_OutwardArm ω n) : aed_GlobalForestArms ω n := by
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
    rw [hbval x hxbox htri]; exact hspec.1
  · intro x hxbox htri y hybox htriy hxy
    have hspecx := (h x hxbox htri).choose_spec
    have hspecy := (h y hybox htriy).choose_spec
    have hxT : x ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
    have hyT : y ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
    have haout : ∀ z ∈ tfc_trifFinset ω n, z ≠ x →
        ¬ Connected d (removeSite x ω) (b x) z := by
      rw [hbval x hxbox htri]; exact hspecx.2.1
    have hfar : Connected d (removeSite x ω) (b y) y := by
      rw [hbval y hybox htriy]; exact hspecy.2.2 x hxT hxy
    exact fld_separate_of_outward_far ω n hxT hyT hxy haout hfar

lemma fld_armEnds_disjoint_of_outward (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x y a a' : Site d}
    (hxT : x ∈ tfc_trifFinset ω n) (hyT : y ∈ tfc_trifFinset ω n) (hxy : x ≠ y)
    (haout : ∀ z ∈ tfc_trifFinset ω n, z ≠ x → ¬ Connected d (removeSite x ω) a z)
    (hfar : Connected d (removeSite x ω) a' y) :
    Disjoint (daep_globalCutArmEnds (tfc_trifFinset ω n) ω n a)
      (daep_globalCutArmEnds (tfc_trifFinset ω n) ω n a') :=
  daep_globalCutArmEnds_disjoint_of_disconnected (tfc_trifFinset ω n) ω n
    (fld_separate_of_outward_far ω n hxT hyT hxy haout hfar)

lemma fld_Tcount_le_boundary_of_outwardArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : fld_OutwardArm ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  aed_Tcount_le_boundary_of_globalForestArms ω n hn (fld_globalForestArms_of_outwardArm ω n h)

lemma fld_outwardArm_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    fld_OutwardArm ω n :=
  fld_outwardArm_of_forestPeel ω n (bkfl_forestPeel_of_noTrif ω n hno)

lemma fld_outwardArm_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    fld_OutwardArm ω n :=
  fld_outwardArm_of_forestPeel ω n
    (bkfl_forestPeel_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq)

lemma fld_outwardArm_of_distinctClusters (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (arm : Site d → Site d)
    (hdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      arm x ∈ box d n ∧ Connected d ω x (arm x) ∧
        (cluster d (removeSites (tfc_trifFinset ω n) ω) (arm x)).Infinite)
    (hfar : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ z ∈ tfc_trifFinset ω n, z ≠ x → Connected d (removeSite z ω) (arm x) x)
    (hsep : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
      IsTrifurcation d ω y → x ≠ y → ¬ Connected d ω x y) :
    fld_OutwardArm ω n :=
  fld_outwardArm_of_forestPeel ω n
    (bkfl_forestPeel_of_distinctClusters ω n arm hdata hfar hsep)

lemma fld_outwardArm_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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
    fld_OutwardArm ω n :=
  fld_outwardArm_of_forestPeel ω n
    (bkfl_forestPeel_of_twoTrif ω n arm hx0y0 htwo hdata_x hdata_y hocc_x hocc_y hfar_x hfar_y)

end Percolation

end StatMech

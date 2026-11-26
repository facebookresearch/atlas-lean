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

/-!
# Private arms of trifurcations

If each trifurcation has an infinite arm that no other connected trifurcation reaches once it is
removed, single cuts separate branches and the Burton–Keane count holds.

## i. Overview

`daepf_PrivateArm ω n` chooses an arm site `b x` for each trifurcation, infinite after all
trifurcations are removed, such that for connected `x ≠ y` the arm of `x` does not contain `y` after
`x` is removed. Each site lies in at most one arm of `x`, so this gives single-cut branch separation
and `Tcount ≤ |∂B_n|`. It holds for at most two trifurcations.

No certificate of this kind can hold for every configuration: each one yields the
trifurcation-to-boundary injection `tfc_DistinctArmEnds`, and `tfc_not_forall_distinctArmEnds` shows
that this injection fails for some configuration in every dimension `d ≥ 1` (in `tfc_lineConfig`
every site is a trifurcation in the sense of `IsTrifurcation`). The certificate is useful
configuration by configuration; the deterministic counting bound is the reusable content.

## ii. Key results

- `StatMech.Percolation.daep2_meets_at_most_one_branch` (in `SingleCutSeparation`) : a site lies in
  at most one arm
- `daepf_singleCutBranchSeparation_of_privateArm` : private arms give single-cut separation
- `daepf_Tcount_le_boundary_of_privateArm` : the counting bound
- `daepf_privateArm_of_twoTrif` : private arms with two trifurcations

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

lemma daepf_in_some_or_no_arm (ω : ConfigSpace (Sym2 (Site d))) {x a₁ a₂ a₃ : Site d}
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) (v : Site d) :
    (Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₂ v ∧
        ¬ Connected d (removeSite x ω) a₃ v) ∨
    (Connected d (removeSite x ω) a₂ v ∧ ¬ Connected d (removeSite x ω) a₁ v ∧
        ¬ Connected d (removeSite x ω) a₃ v) ∨
    (Connected d (removeSite x ω) a₃ v ∧ ¬ Connected d (removeSite x ω) a₁ v ∧
        ¬ Connected d (removeSite x ω) a₂ v) ∨
    (¬ Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₂ v ∧
        ¬ Connected d (removeSite x ω) a₃ v) := by
  classical
  by_cases h1 : Connected d (removeSite x ω) a₁ v
  · exact Or.inl ⟨h1, fun h2 => hd12 (h1.trans h2.symm), fun h3 => hd13 (h1.trans h3.symm)⟩
  · by_cases h2 : Connected d (removeSite x ω) a₂ v
    · exact Or.inr (Or.inl ⟨h2, h1, fun h3 => hd23 (h2.trans h3.symm)⟩)
    · by_cases h3 : Connected d (removeSite x ω) a₃ v
      · exact Or.inr (Or.inr (Or.inl ⟨h3, h1, h2⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩))

/-- Private arms for `B_n`: each trifurcation has an arm site whose cluster stays infinite after all
trifurcations are removed and which, for connected trifurcations `x ≠ y`, does not reach `y`
once `x` is removed. -/
def daepf_PrivateArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y →
      ¬ Connected d (removeSite x ω) (b x) y ∧
        Connected d (removeSite x ω) (b y) y)

lemma daepf_singleCutBranchSeparation_of_privateArm (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : daepf_PrivateArm ω n) :
    daep2_SingleCutBranchSeparation ω n := by
  obtain ⟨b, hb, hpair⟩ := h
  refine ⟨b, hb, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn
  obtain ⟨hpriv, hfar⟩ := hpair x hxbox htri y hybox htriy hxy hconn
  intro hbxby
  exact hpriv (hbxby.trans hfar)

lemma daepf_privateArm_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    daepf_PrivateArm ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri _ _ _ _ _; exact absurd htri (hno x hxbox)

lemma daepf_privateArm_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    daepf_PrivateArm ω n := by
  classical
  have hT : tfc_trifFinset ω n = {x₀} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨tfc_mem_trifFinset.mpr ⟨hx0box, htri0⟩, ?_⟩
    intro y hy
    rw [tfc_mem_trifFinset] at hy
    exact huniq y hy.1 hy.2
  have hcut : removeSites (tfc_trifFinset ω n) ω = removeSite x₀ ω := by
    rw [hT, daep_removeSites_singleton]
  refine ⟨fun _ => a, ?_, ?_⟩
  · intro x hxbox htri
    have hx0 : x = x₀ := huniq x hxbox htri
    subst hx0
    refine ⟨habox, haconn, ?_⟩
    rw [hcut]; exact hainf
  · intro x hxbox htri y hybox htriy hxy _
    exact absurd ((huniq x hxbox htri).trans (huniq y hybox htriy).symm) hxy

lemma daepf_privateArm_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d)
    (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hpriv_xy : ¬ Connected d (removeSite x₀ ω) (b x₀) y₀)
    (hfar_xy : Connected d (removeSite x₀ ω) (b y₀) y₀)
    (hpriv_yx : ¬ Connected d (removeSite y₀ ω) (b y₀) x₀)
    (hfar_yx : Connected d (removeSite y₀ ω) (b x₀) x₀) :
    daepf_PrivateArm ω n := by
  classical
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hbx0
    · exact hby0
  · intro x hxbox htri y hybox htriy hxy hconn
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo y hybox htriy with rfl | rfl
      · exact absurd rfl hxy
      · exact ⟨hpriv_xy, hfar_xy⟩
    · rcases htwo y hybox htriy with rfl | rfl
      · exact ⟨hpriv_yx, hfar_yx⟩
      · exact absurd rfl hxy

lemma daepf_Tcount_le_boundary_of_privateArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : daepf_PrivateArm ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  daep2_Tcount_le_boundary_of_singleCut ω n hn
    (daepf_singleCutBranchSeparation_of_privateArm ω n h)

end Percolation

end StatMech

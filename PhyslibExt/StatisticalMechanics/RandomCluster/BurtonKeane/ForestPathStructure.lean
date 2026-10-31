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
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndDisjoint
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DivergentArmOrder
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClawDivergentArmOrder
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PairwiseCutSeparation

/-!
# Two-sided private far arms

If every pair of connected trifurcations has a private infinite arm on at least one side, the
trifurcations have pairwise cut separation and the Burton–Keane count holds.

## i. Overview

`fps_TwoSidedPrivateFar ω n` chooses for each trifurcation `x` an arm site `b x` in the box whose
cluster stays infinite after all trifurcations are removed, such that for any two connected
trifurcations one of them separates its arm from the other. This gives `fac_PairwiseCutSeparation`,
hence global forest arms and `Tcount ≤ |∂B_n|`. The certificate holds trivially with at most two
trifurcations and follows from a private arm for each trifurcation.

No certificate of this kind can hold for every configuration: each one yields the
trifurcation-to-boundary injection `tfc_DistinctArmEnds`, and `tfc_not_forall_distinctArmEnds` shows
that this injection fails for some configuration in every dimension `d ≥ 1` (in `tfc_lineConfig`
every site is a trifurcation in the sense of `IsTrifurcation`). The certificate is useful
configuration by configuration; the deterministic counting bound is the reusable content.

## ii. Key results

- `fps_pairwiseCutSeparation_of_twoSidedPrivateFar` : two-sided private arms give pairwise cut
  separation
- `fps_Tcount_le_boundary_of_twoSidedPrivateFar` : the counting bound
- `fps_twoSidedPrivateFar_of_privateArm` : a private arm for each trifurcation suffices

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

lemma fps_cutX_sep_of_privateFar_x (ω : ConfigSpace (Sym2 (Site d))) {x bx by_ y : Site d}
    (hpriv : ¬ Connected d (removeSite x ω) bx y)
    (hfar : Connected d (removeSite x ω) by_ y) :
    ¬ Connected d (removeSite x ω) bx by_ := by
  intro hbxby
  exact hpriv (hbxby.trans hfar)

lemma fps_cutY_sep_of_privateFar_y (ω : ConfigSpace (Sym2 (Site d))) {y bx by_ x : Site d}
    (hpriv : ¬ Connected d (removeSite y ω) by_ x)
    (hfar : Connected d (removeSite y ω) bx x) :
    ¬ Connected d (removeSite y ω) bx by_ := by
  intro hbxby
  exact hpriv (hbxby.symm.trans hfar)

lemma fps_eitherCut_sep_of_twoSidedPrivateFar (ω : ConfigSpace (Sym2 (Site d)))
    {x y bx by_ : Site d}
    (hprivx : ¬ Connected d (removeSite x ω) bx y)
    (hprivy : ¬ Connected d (removeSite y ω) by_ x)
    (hfar : Connected d (removeSite x ω) by_ y ∨ Connected d (removeSite y ω) bx x) :
    ¬ Connected d (removeSite x ω) bx by_ ∨ ¬ Connected d (removeSite y ω) bx by_ := by
  rcases hfar with hfarx | hfary
  · exact Or.inl (fps_cutX_sep_of_privateFar_x ω hprivx hfarx)
  · exact Or.inr (fps_cutY_sep_of_privateFar_y ω hprivy hfary)

/-- Two-sided private far arms for `B_n`: each trifurcation has an arm site in the box whose cluster
stays infinite after all trifurcations are removed, and of any two connected trifurcations at
least one separates its own arm from the other. -/
def fps_TwoSidedPrivateFar (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y →
      (¬ Connected d (removeSite x ω) (b x) y) ∧
      (¬ Connected d (removeSite y ω) (b y) x) ∧
      (Connected d (removeSite x ω) (b y) y ∨ Connected d (removeSite y ω) (b x) x))

lemma fps_pairwiseCutSeparation_of_twoSidedPrivateFar (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : fps_TwoSidedPrivateFar ω n) :
    fac_PairwiseCutSeparation ω n := by
  obtain ⟨b, hdata, hpair⟩ := h
  refine ⟨b, hdata, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn
  obtain ⟨hprivx, hprivy, hfar⟩ := hpair x hxbox htri y hybox htriy hxy hconn
  exact fps_eitherCut_sep_of_twoSidedPrivateFar ω hprivx hprivy hfar

lemma fps_globalForestArms_of_twoSidedPrivateFar (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : fps_TwoSidedPrivateFar ω n) :
    aed_GlobalForestArms ω n :=
  fac_globalForestArms_of_pairwiseCutSeparation ω n
    (fps_pairwiseCutSeparation_of_twoSidedPrivateFar ω n h)

lemma fps_twoSidedPrivateFar_of_privateArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : daepf_PrivateArm ω n) :
    fps_TwoSidedPrivateFar ω n := by
  obtain ⟨b, hdata, hpair⟩ := h
  refine ⟨b, hdata, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn
  obtain ⟨hprivx, hfarx⟩ := hpair x hxbox htri y hybox htriy hxy hconn
  obtain ⟨hprivy, _⟩ := hpair y hybox htriy x hxbox htri (Ne.symm hxy) hconn.symm
  exact ⟨hprivx, hprivy, Or.inl hfarx⟩

lemma fps_eitherCut_sep_via_farY_only (ω : ConfigSpace (Sym2 (Site d)))
    {x y bx by_ : Site d}
    (hprivy : ¬ Connected d (removeSite y ω) by_ x)
    (hfary : Connected d (removeSite y ω) bx x) :
    ¬ Connected d (removeSite y ω) bx by_ :=
  fps_cutY_sep_of_privateFar_y ω hprivy hfary

lemma fps_twoSidedPrivateFar_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    fps_TwoSidedPrivateFar ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri _ _ _ _ _; exact absurd htri (hno x hxbox)

lemma fps_twoSidedPrivateFar_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    fps_TwoSidedPrivateFar ω n :=
  fps_twoSidedPrivateFar_of_privateArm ω n
    (daepf_privateArm_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq)

lemma fps_twoSidedPrivateFar_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d) (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hpriv_xy : ¬ Connected d (removeSite x₀ ω) (b x₀) y₀)
    (hpriv_yx : ¬ Connected d (removeSite y₀ ω) (b y₀) x₀)
    (hfar_xy : Connected d (removeSite x₀ ω) (b y₀) y₀)
    (hfar_yx : Connected d (removeSite y₀ ω) (b x₀) x₀) :
    fps_TwoSidedPrivateFar ω n := by
  classical
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hbx0
    · exact hby0
  · intro x hxbox htri y hybox htriy hxy _hconn
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo y hybox htriy with rfl | rfl
      · exact absurd rfl hxy
      · exact ⟨hpriv_xy, hpriv_yx, Or.inl hfar_xy⟩
    · rcases htwo y hybox htriy with rfl | rfl
      · exact ⟨hpriv_yx, hpriv_xy, Or.inr hfar_xy⟩
      · exact absurd rfl hxy

lemma fps_Tcount_le_boundary_of_twoSidedPrivateFar (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : fps_TwoSidedPrivateFar ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  fac_Tcount_le_boundary_of_pairwiseCutSeparation ω n hn
    (fps_pairwiseCutSeparation_of_twoSidedPrivateFar ω n h)

end Percolation

end StatMech

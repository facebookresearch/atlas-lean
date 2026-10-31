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
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPeel
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DivergentArmOrder
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClawDivergentArmOrder
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootedSpanningForest
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoverArmDivergence
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootedTreeArmSelection
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateFarForest
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmDivergenceRank
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CutAvoidingRayArm

/-!
# Self down arms

A down neighbour for each trifurcation, ranked so that arms point away from lower trifurcations,
gives rooted arm divergence and the trifurcation count.

## i. Overview

`bc36_SelfDownArm ω n` chooses infinite arm sites, a rank injective on connected trifurcations, and
for each trifurcation a down neighbour such that the chosen arm avoids the side of every lower
connected trifurcation. It gives rooted arm divergence and `Tcount ≤ |∂B_n|`. It holds with at most
two trifurcations, for a four-vertex tree, for claws, and under single-cut separation.

No certificate of this kind can hold for every configuration: each one yields the
trifurcation-to-boundary injection `tfc_DistinctArmEnds`, and `tfc_not_forall_distinctArmEnds` shows
that this injection fails for some configuration in every dimension `d ≥ 1` (in `tfc_lineConfig`
every site is a trifurcation in the sense of `IsTrifurcation`). The certificate is useful
configuration by configuration; the deterministic counting bound is the reusable content.

## ii. Key results

- `bc36_rootedArmDivergence_of_selfDownArm` : self down arms give rooted arm divergence
- `bc36_selfDownArm_of_singleCutSep` : single-cut separation gives self down arms
- `bc36_Tcount_le_boundary_of_selfDownArm` : the counting bound

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

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Results -/

/-- Self down arms for `B_n`: infinite arm sites, a rank injective on connected trifurcations and a
down neighbour for each trifurcation such that its arm avoids the side of every lower connected
trifurcation. -/
def bc36_SelfDownArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (b : Site d → Site d) (rank : Site d → ℕ ×ₗ ℕ) (dn : Site d → Site d),
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x ≠ rank y) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x < rank y →
      Connected d (removeSite y ω) (dn y) (b y) ∧
      ¬ Connected d (removeSite y ω) (dn y) (b x))

lemma bc36_rootedArmDivergence_of_selfDownArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc36_SelfDownArm ω n) : rfp_RootedArmDivergence ω n := by
  obtain ⟨b, rank, dn, hdata, hrank, hplace⟩ := h
  refine ⟨b, rank, hdata, hrank, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hself, havoid⟩ := hplace x hxbox htri y hybox htriy hxy hconn hlt
  have hyT : y ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
  have hbxnotin : b x ∉ tfc_trifFinset ω n :=
    stac_infiniteCluster_notMem (tfc_trifFinset ω n) ω (hdata x hxbox htri).2.2
  have hbynotin : b y ∉ tfc_trifFinset ω n :=
    stac_infiniteCluster_notMem (tfc_trifFinset ω n) ω (hdata y hybox htriy).2.2
  have hne_y_bx : y ≠ b x := fun heq => hbxnotin (heq ▸ hyT)
  have hne_y_by : y ≠ b y := fun heq => hbynotin (heq ▸ hyT)
  have hy_bx : Connected d ω y (b x) := hconn.symm.trans (hdata x hxbox htri).2.1
  have hy_by : Connected d ω y (b y) := (hdata y hybox htriy).2.1
  have hsep : ¬ Connected d (removeSite y ω) (b y) (b x) :=
    bkfl_arms_separate ω havoid hself (bkfl_inArm_self ω y (b x))
  intro hsame
  exact hsep ((fsp_armWitness_inArm ω hy_by hne_y_by).symm.trans
    (hsame.symm.trans (fsp_armWitness_inArm ω hy_bx hne_y_bx)))

lemma bc36_selfDownArm_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc36_SelfDownArm ω n := by
  refine ⟨id, (fun _ => toLex (0, 0)), id, ?_, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)

lemma bc36_selfDownArm_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d) (dn : Site d → Site d) (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hself : Connected d (removeSite y₀ ω) (dn y₀) (b y₀))
    (havoid : ¬ Connected d (removeSite y₀ ω) (dn y₀) (b x₀)) :
    bc36_SelfDownArm ω n := by
  classical
  refine ⟨b, (fun z => if z = y₀ then toLex (1, 0) else toLex (0, 0)), dn, ?_, ?_, ?_⟩
  · intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hbx0
    · exact hby0
  · intro x hxbox htri y hybox htriy hxy _
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo y hybox htriy with rfl | rfl
      · exact absurd rfl hxy
      · simp only [ite_eq_right hx0y0, ite_eq_left]; exact stt_lex_ne_fst (by norm_num)
    · rcases htwo y hybox htriy with rfl | rfl
      · simp only [ite_eq_right hx0y0, ite_eq_left]; exact stt_lex_ne_fst (by norm_num)
      · exact absurd rfl hxy
  · intro x hxbox htri y hybox htriy hxy _ hlt
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo y hybox htriy with rfl | rfl
      · exact absurd rfl hxy
      · exact ⟨hself, havoid⟩
    · rcases htwo y hybox htriy with rfl | rfl
      · simp only [ite_eq_right hx0y0, ite_eq_left] at hlt
        exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
      · exact absurd rfl hxy

set_option linter.unusedSimpArgs false in
lemma bc36_selfDownArm_of_fourTree (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ m g h : Site d} (b : Site d → Site d)
    (hx0m : x₀ ≠ m) (hx0g : x₀ ≠ g) (hx0h : x₀ ≠ h) (hmg : m ≠ g) (hmh : m ≠ h) (hgh : g ≠ h)
    (hfour : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g ∨ x = h)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hbm : b m ∈ box d n ∧ Connected d ω m (b m) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b m)).Infinite)
    (hbg : b g ∈ box d n ∧ Connected d ω g (b g) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b g)).Infinite)
    (hbh : b h ∈ box d n ∧ Connected d ω h (b h) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b h)).Infinite)
    (hm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
    (hg_x0 : ¬ Connected d (removeSite g ω) (b g) (b x₀))
    (hg_m : ¬ Connected d (removeSite g ω) (b g) (b m))
    (hh_x0 : ¬ Connected d (removeSite h ω) (b h) (b x₀))
    (hh_m : ¬ Connected d (removeSite h ω) (b h) (b m))
    (hh_g : ¬ Connected d (removeSite h ω) (b h) (b g)) :
    bc36_SelfDownArm ω n := by
  classical
  refine ⟨b, (fun z => if z = x₀ then toLex (0, 0) else if z = m then toLex (1, 0)
              else if z = g then toLex (2, 0) else toLex (3, 0)), b, ?_, ?_, ?_⟩
  · intro x hxbox htri
    rcases hfour x hxbox htri with rfl | rfl | rfl | rfl
    · exact hbx0
    · exact hbm
    · exact hbg
    · exact hbh
  · intro x hxbox htri y hybox htriy hxy _
    simp only
    rcases hfour x hxbox htri with rfl | rfl | rfl | rfl <;>
      rcases hfour y hybox htriy with rfl | rfl | rfl | rfl <;>
      simp only [↓reduceIte, ite_eq_right hx0m.symm, ite_eq_right hx0g.symm, ite_eq_right hx0h.symm,
        ite_eq_right hmg.symm, ite_eq_right hmh.symm, ite_eq_right hgh.symm] <;>
      first
      | exact absurd rfl hxy
      | exact stt_lex_ne_fst (by norm_num)
  · intro x hxbox htri y hybox htriy hxy _ hlt
    refine ⟨connected_rfl, ?_⟩
    simp only at hlt
    rcases hfour y hybox htriy with rfl | rfl | rfl | rfl <;>
      rcases hfour x hxbox htri with rfl | rfl | rfl | rfl <;>
      simp only [↓reduceIte, ite_eq_right hx0m, ite_eq_right hx0g, ite_eq_right hx0h,
        ite_eq_right hmg, ite_eq_right hmh,
        ite_eq_right hgh, ite_eq_right hx0m.symm, ite_eq_right hx0g.symm, ite_eq_right hx0h.symm,
          ite_eq_right hmg.symm,
        ite_eq_right hmh.symm, ite_eq_right hgh.symm] at hlt <;>
      first
      | exact absurd rfl hxy
      | exact hm
      | exact hg_x0
      | exact hg_m
      | exact hh_x0
      | exact hh_m
      | exact hh_g
      | exact absurd hlt (stt_lex_not_lt_fst (by norm_num))

lemma bc36_selfDownArm_of_singleCutSep (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : fcc_RootedSingleCutSeparation ω n) : bc36_SelfDownArm ω n := by
  obtain ⟨b, rank, hdata, hrank, hsep⟩ := h
  refine ⟨b, rank, b, hdata, hrank, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  exact ⟨connected_rfl, fun hc => hsep x hxbox htri y hybox htriy hxy hconn hlt hc.symm⟩

lemma bc36_selfDownArm_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (lx : Site d → Fin 3) (ly : Fin 3 → Site d → Fin 3)
    (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧
      Connected d ω x₀ (y i))
    (hyinj : Function.Injective y)
    (hlyf : ∀ i u v, Connected d ω (y i) u → y i ≠ u → Connected d ω (y i) v → y i ≠ v →
      (ly i u = ly i v ↔ fsp_sameArm ω (y i) u v))
    (hGstar : ∀ i w, Connected d ω x₀ w → x₀ ≠ w → Connected d ω (y i) w → y i ≠ w →
      (ly i w = 0 ↔ lx w ≠ i))
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
    (b : Site d → Site d)
    (hbdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
    (hcy : ∀ i, lx (b (y i)) = i)
    {j₀ : Fin 3} (hcx : lx (b x₀) = j₀)
    (hcentral : ly j₀ (b x₀) ≠ ly j₀ (b (y j₀))) :
    bc36_SelfDownArm ω n :=
  bc36_selfDownArm_of_singleCutSep ω n
    (fcc_rootedSingleCutSeparation_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlyf hGstar
      hsingle b hbdata hcy hcx hcentral)

lemma bc36_Tcount_le_boundary_of_selfDownArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : bc36_SelfDownArm ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bc28_Tcount_le_boundary_of_rootedArmDivergence ω n hn
    (bc36_rootedArmDivergence_of_selfDownArm ω n h)

end StatMech.Walls

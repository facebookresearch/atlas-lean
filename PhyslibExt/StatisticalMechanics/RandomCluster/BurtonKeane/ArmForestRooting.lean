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
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPeel
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DivergentArmOrder
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoverArmDivergence
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClawDivergentArmOrder
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootedSpanningForest
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateFarForest
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CutAvoidingRayArm
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootedSelfDivergence

/-!
# Arm adjacency, down-arm selectors and parent funnelling

Down-arm selectors, arm forest rootings and parent funnelling are equivalent ways to root the
trifurcations of a box; each gives the self-down-arm property and the trifurcation count.

## i. Overview

`bc37_DownArmSelector` chooses arm ends and a rank so that removing a higher-ranked trifurcation
separates its end from the lower-ranked ends. Two trifurcations are arm-adjacent
(`bc37_ArmAdjacent`) when they are connected after all other trifurcations of the box are removed
(`bc37_cutExcept`); the arm-adjacency graph `bc37_armAdjGraph` is a subgraph of the trifurcation
graph. The arm forest rooting `bc37_ArmForestRooting` is equivalent to a down-arm selector, and
parent funnelling `bc37_ParentFunneling` gives one. All give the self-down-arm property
`bc36_SelfDownArm` and the bound `Tcount ≤ |∂Λₙ|`. They hold with no trifurcation, two
trifurcations, a chain of three, a claw, or a tree of four.

The configuration-wide form of these conditions, for every configuration and every box of radius
`n ≥ 1`, is unsatisfiable when `d ≥ 1`: it implies `Tcount d ω n ≤ boxSV_boundaryCard d n` for every
configuration, which `tfc_not_forall_Tcount_le_boundary` refutes
(`bc37_not_forall_armForestRooting`, `bc37_not_forall_parentFunneling`). The Burton–Keane theorems
that assumed them were removed as vacuous.

## ii. Key results

- `bc37_armForestRooting_iff_downArmSelector` : arm forest rootings are down-arm selectors.
- `bc37_Tcount_le_boundary_of_parentFunneling` : the count bound from parent funnelling.

## iii. Table of contents

- A. Down-arm selectors
- B. Arm adjacency
- C. Arm forest rooting
- D. Parent funnelling
- E. Unsatisfiability of the configuration-wide conditions

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Down-arm selectors -/

/-- Down-arm selector for the box of radius `n`: arm ends `b x` and a rank separating connected
trifurcations, such that removing the higher-ranked of two connected trifurcations separates its end
from the end of the lower one. -/
def bc37_DownArmSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (b : Site d → Site d) (rank : Site d → ℕ ×ₗ ℕ),
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x ≠ rank y) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x < rank y →
      ¬ Connected d (removeSite y ω) (b y) (b x))

lemma bc37_selfDownArm_of_downArmSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc37_DownArmSelector ω n) : bc36_SelfDownArm ω n := by
  obtain ⟨b, rank, hdata, hrank, hdiv⟩ := h
  refine ⟨b, rank, b, hdata, hrank, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  exact ⟨connected_rfl, hdiv x hxbox htri y hybox htriy hxy hconn hlt⟩

lemma bc37_rootedArmDivergence_of_downArmSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc37_DownArmSelector ω n) : rfp_RootedArmDivergence ω n :=
  bc36_rootedArmDivergence_of_selfDownArm ω n (bc37_selfDownArm_of_downArmSelector ω n h)

/-! ## B. Arm adjacency -/

/-- The configuration with every trifurcation of the box except `x` and `y` removed. -/
noncomputable def bc37_cutExcept (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x y : Site d) :
    ConfigSpace (Sym2 (Site d)) :=
  removeSites ((tfc_trifFinset ω n).erase x |>.erase y) ω

/-- `x` and `y` are distinct, connected, and still connected after all other trifurcations of the
box
are removed. -/
def bc37_ArmAdjacent (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x y : Site d) : Prop :=
  x ≠ y ∧ Connected d ω x y ∧ Connected d (bc37_cutExcept ω n x y) x y

lemma bc37_armAdjacent_symm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) {x y : Site d}
    (h : bc37_ArmAdjacent ω n x y) : bc37_ArmAdjacent ω n y x := by
  obtain ⟨hne, hconn, hcut⟩ := h
  refine ⟨hne.symm, hconn.symm, ?_⟩
  have hset : ((tfc_trifFinset ω n).erase y).erase x
      = ((tfc_trifFinset ω n).erase x).erase y := Finset.erase_right_comm
  unfold bc37_cutExcept
  rw [hset]
  exact hcut.symm

lemma bc37_armAdjacent_irrefl (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x : Site d) :
    ¬ bc37_ArmAdjacent ω n x x := fun ⟨hne, _, _⟩ => hne rfl

/-- The arm-adjacency graph on the trifurcations of the box. -/
def bc37_armAdjGraph (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    SimpleGraph {x : Site d // x ∈ tfc_trifFinset ω n} where
  Adj a b := bc37_ArmAdjacent ω n a.1 b.1
  symm := ⟨fun _ _ h => bc37_armAdjacent_symm ω n h⟩
  loopless := ⟨fun a h => bc37_armAdjacent_irrefl ω n a.1 h⟩

lemma bc37_armAdjGraph_le_trifGraph (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc37_armAdjGraph ω n ≤ stt_trifGraph ω n := by
  intro a b hab
  exact ⟨fun h => hab.1 (congrArg Subtype.val h), hab.2.1⟩

lemma bc37_sameCluster_of_armAdjReachable (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {a b : {x : Site d // x ∈ tfc_trifFinset ω n}} (h : (bc37_armAdjGraph ω n).Reachable a b) :
    Connected d ω a.1 b.1 :=
  (stt_reachable_iff ω n a b).mp (h.mono (bc37_armAdjGraph_le_trifGraph ω n))

lemma bc37_isForest_iff_isAcyclic (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    (bc37_armAdjGraph ω n).IsAcyclic ↔ ∀ ⦃a b⦄ (p q : (bc37_armAdjGraph ω n).Path a b), p = q :=
  SimpleGraph.isAcyclic_iff_subsingleton_path.trans
    ⟨fun h a b p q => (h a b).elim p q, fun h _a _b => ⟨fun p q => h p q⟩⟩

/-! ## C. Arm forest rooting -/

/-- Arm forest rooting: arm ends `b x`, a rank and an arm-parent map `A` such that each
trifurcation's
end funnels through its arm parent. -/
def bc37_ArmForestRooting (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (b : Site d → Site d) (rank : Site d → ℕ ×ₗ ℕ) (A : Site d → Site d),
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x ≠ rank y) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x < rank y →
      Connected d (removeSite y ω) (A y) (b y) ∧
      ¬ Connected d (removeSite y ω) (A y) (b x))

lemma bc37_downArmSelector_of_armForestRooting (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc37_ArmForestRooting ω n) : bc37_DownArmSelector ω n := by
  obtain ⟨b, rank, A, hdata, hrank, hplace⟩ := h
  refine ⟨b, rank, hdata, hrank, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hdown, hbetween⟩ := hplace x hxbox htri y hybox htriy hxy hconn hlt
  exact bkfl_arms_separate ω hbetween hdown (bkfl_inArm_self ω y (b x))

lemma bc37_selfDownArm_of_armForestRooting (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc37_ArmForestRooting ω n) : bc36_SelfDownArm ω n :=
  bc37_selfDownArm_of_downArmSelector ω n (bc37_downArmSelector_of_armForestRooting ω n h)

lemma bc37_armForestRooting_of_downArmSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc37_DownArmSelector ω n) : bc37_ArmForestRooting ω n := by
  obtain ⟨b, rank, hdata, hrank, hdiv⟩ := h
  refine ⟨b, rank, b, hdata, hrank, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  exact ⟨connected_rfl, hdiv x hxbox htri y hybox htriy hxy hconn hlt⟩

lemma bc37_armForestRooting_iff_downArmSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc37_ArmForestRooting ω n ↔ bc37_DownArmSelector ω n :=
  ⟨bc37_downArmSelector_of_armForestRooting ω n, bc37_armForestRooting_of_downArmSelector ω n⟩

lemma bc37_downArmSelector_of_singleCutSep (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : fcc_RootedSingleCutSeparation ω n) : bc37_DownArmSelector ω n := by
  obtain ⟨b, rank, hdata, hrank, hsep⟩ := h
  refine ⟨b, rank, hdata, hrank, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  exact fun hc => hsep x hxbox htri y hybox htriy hxy hconn hlt hc.symm

lemma bc37_armForestRooting_of_singleCutSep (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : fcc_RootedSingleCutSeparation ω n) : bc37_ArmForestRooting ω n :=
  bc37_armForestRooting_of_downArmSelector ω n (bc37_downArmSelector_of_singleCutSep ω n h)

/-! ## D. Parent funnelling -/

/-- Parent funnelling: arm ends, a rank and a parent map such that removing a trifurcation separates
its
end from its parent while the ends of lower trifurcations still reach the parent. -/
def bc37_ParentFunneling (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (b : Site d → Site d) (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x ≠ rank y) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x < rank y →
      (¬ Connected d (removeSite y ω) (b y) (b (par y))) ∧
      (¬ Connected d (removeSite y ω) (b y) (par y)) ∧
      (x ≠ par y → Connected d (removeSite y ω) (b x) (par y)))

lemma bc37_downArmSelector_of_parentFunneling (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc37_ParentFunneling ω n) : bc37_DownArmSelector ω n := by
  obtain ⟨b, rank, par, hdata, hrank, hpar⟩ := h
  refine ⟨b, rank, hdata, hrank, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hlocal, hself, hfunnel⟩ := hpar x hxbox htri y hybox htriy hxy hconn hlt
  by_cases hxpar : x = par y
  · rw [hxpar]; exact hlocal
  · intro hconn_by_bx
    exact hself (hconn_by_bx.trans (hfunnel hxpar))

lemma bc37_selfDownArm_of_parentFunneling (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc37_ParentFunneling ω n) : bc36_SelfDownArm ω n :=
  bc37_selfDownArm_of_downArmSelector ω n (bc37_downArmSelector_of_parentFunneling ω n h)

lemma bc37_armForestRooting_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc37_ArmForestRooting ω n := by
  refine ⟨id, (fun _ => toLex (0, 0)), id, ?_, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)

lemma bc37_armForestRooting_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d) (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hdiv : ¬ Connected d (removeSite y₀ ω) (b y₀) (b x₀)) :
    bc37_ArmForestRooting ω n := by
  classical
  apply bc37_armForestRooting_of_downArmSelector
  refine ⟨b, (fun z => if z = y₀ then toLex (1, 0) else toLex (0, 0)), ?_, ?_, ?_⟩
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
      · exact hdiv
    · rcases htwo y hybox htriy with rfl | rfl
      · simp only [ite_eq_right hx0y0, ite_eq_left] at hlt
        exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
      · exact absurd rfl hxy

set_option linter.unusedSimpArgs false in
lemma bc37_armForestRooting_of_threeChain (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ m g : Site d} (b : Site d → Site d)
    (hx0m : x₀ ≠ m) (hx0g : x₀ ≠ g) (hmg : m ≠ g)
    (hthree : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hbm : b m ∈ box d n ∧ Connected d ω m (b m) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b m)).Infinite)
    (hbg : b g ∈ box d n ∧ Connected d ω g (b g) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b g)).Infinite)
    (hsxm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
    (hsxg : ¬ Connected d (removeSite g ω) (b g) (b x₀))
    (hsmg : ¬ Connected d (removeSite g ω) (b g) (b m)) :
    bc37_ArmForestRooting ω n := by
  classical
  apply bc37_armForestRooting_of_downArmSelector
  refine ⟨b, (fun z => if z = x₀ then toLex (0, 0)
              else if z = m then toLex (1, 0) else toLex (2, 0)), ?_, ?_, ?_⟩
  · intro x hxbox htri
    rcases hthree x hxbox htri with rfl | rfl | rfl
    · exact hbx0
    · exact hbm
    · exact hbg
  · intro x hxbox htri y hybox htriy hxy _
    simp only
    rcases hthree x hxbox htri with rfl | rfl | rfl <;>
      rcases hthree y hybox htriy with rfl | rfl | rfl <;>
      simp only [↓reduceIte, ite_eq_right hx0m.symm, ite_eq_right hx0g.symm, ite_eq_right hmg.symm,
        ite_eq_right hx0m, ite_eq_right hx0g, ite_eq_right hmg] <;>
      first
      | exact absurd rfl hxy
      | exact stt_lex_ne_fst (by norm_num)
  · intro x hxbox htri y hybox htriy hxy _ hlt
    simp only at hlt
    rcases hthree y hybox htriy with rfl | rfl | rfl <;>
      rcases hthree x hxbox htri with rfl | rfl | rfl <;>
      simp only [↓reduceIte, ite_eq_right hx0m, ite_eq_right hx0g, ite_eq_right hmg,
        ite_eq_right hx0m.symm, ite_eq_right hx0g.symm, ite_eq_right hmg.symm] at hlt ⊢ <;>
      first
      | exact absurd rfl hxy
      | exact hsxm
      | exact hsxg
      | exact hsmg
      | exact absurd hlt (stt_lex_not_lt_fst (by norm_num))

lemma bc37_armForestRooting_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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
    bc37_ArmForestRooting ω n :=
  bc37_armForestRooting_of_singleCutSep ω n
    (fcc_rootedSingleCutSeparation_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlyf hGstar
      hsingle b hbdata hcy hcx hcentral)

set_option linter.unusedSimpArgs false in
lemma bc37_armForestRooting_of_fourTree (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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
    bc37_ArmForestRooting ω n := by
  classical
  apply bc37_armForestRooting_of_downArmSelector
  refine ⟨b, (fun z => if z = x₀ then toLex (0, 0) else if z = m then toLex (1, 0)
              else if z = g then toLex (2, 0) else toLex (3, 0)), ?_, ?_, ?_⟩
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

lemma bc37_Tcount_le_boundary_of_armForestRooting (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : bc37_ArmForestRooting ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bc36_Tcount_le_boundary_of_selfDownArm ω n hn (bc37_selfDownArm_of_armForestRooting ω n h)

lemma bc37_parentFunneling_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc37_ParentFunneling ω n := by
  refine ⟨id, (fun _ => toLex (0, 0)), id, ?_, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)

lemma bc37_parentFunneling_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d) (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hlocal : ¬ Connected d (removeSite y₀ ω) (b y₀) (b x₀))
    (hself : ¬ Connected d (removeSite y₀ ω) (b y₀) x₀) :
    bc37_ParentFunneling ω n := by
  classical
  refine ⟨b, (fun z => if z = y₀ then toLex (1, 0) else toLex (0, 0)),
    (fun _ => x₀), ?_, ?_, ?_⟩
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
      · exact ⟨hlocal, hself, fun hne => absurd rfl hne⟩
    · rcases htwo y hybox htriy with rfl | rfl
      · simp only [ite_eq_right hx0y0, ite_eq_left] at hlt
        exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
      · exact absurd rfl hxy

lemma bc37_parentFunneling_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (b : Site d → Site d)
    (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧
      Connected d ω x₀ (y i))
    (hyinj : Function.Injective y)
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby : ∀ i, b (y i) ∈ box d n ∧ Connected d ω (y i) (b (y i)) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b (y i))).Infinite)
    (hloc : ∀ i, ¬ Connected d (removeSite (y i) ω) (b (y i)) (b x₀))
    (hself : ∀ i, ¬ Connected d (removeSite (y i) ω) (b (y i)) x₀)
    (hfun : ∀ i j : Fin 3, (j : ℕ) < i →
      Connected d (removeSite (y i) ω) (b (y j)) x₀) :
    bc37_ParentFunneling ω n := by
  classical
  set rank : Site d → ℕ ×ₗ ℕ := fun z =>
    if z = x₀ then toLex (0, 0)
    else if h : ∃ i, z = y i then toLex (1, (h.choose : ℕ)) else toLex (2, 0) with hrank
  have hrx0 : rank x₀ = toLex (0, 0) := by simp only [hrank, ite_eq_left rfl]
  have hry : ∀ i, rank (y i) = toLex (1, (i : ℕ)) := by
    intro i
    have hne : y i ≠ x₀ := (hydata i).2.2.1.symm
    have hex : ∃ k, y i = y k := ⟨i, rfl⟩
    have hchoose : hex.choose = i := hyinj hex.choose_spec.symm
    simp only [hrank, ite_eq_right hne, dite_eq_left hex, hchoose]
  refine ⟨b, rank, (fun _ => x₀), ?_, ?_, ?_⟩
  · intro x hxbox htri
    rcases hsingle x hxbox htri with rfl | ⟨i, rfl⟩
    · exact hbx0
    · exact hby i
  · intro x hxbox htri yv hyvbox htriv hxy _
    rcases hsingle x hxbox htri with rfl | ⟨i, rfl⟩ <;>
      rcases hsingle yv hyvbox htriv with rfl | ⟨j, rfl⟩
    · exact absurd rfl hxy
    · rw [hrx0, hry j]; exact stt_lex_ne_fst (by norm_num)
    · rw [hrx0, hry i]; exact (stt_lex_ne_fst (by norm_num)).symm
    · rw [hry i, hry j]
      have hij : i ≠ j := fun h => hxy (congrArg y h)
      exact stt_lex_ne_snd (fun he => hij (Fin.ext he))
  · intro x hxbox htri yv hyvbox htriv hxy hconn hlt
    rcases hsingle yv hyvbox htriv with rfl | ⟨i, rfl⟩
    · rcases hsingle x hxbox htri with rfl | ⟨j, rfl⟩
      · exact absurd rfl hxy
      · rw [hry j, hrx0] at hlt; exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · refine ⟨hloc i, hself i, ?_⟩
      intro hxne
      rcases hsingle x hxbox htri with rfl | ⟨j, rfl⟩
      · exact absurd rfl hxne
      · rw [hry j, hry i] at hlt
        have hji : (j : ℕ) < i := by
          rw [Prod.Lex.toLex_lt_toLex] at hlt
          rcases hlt with hh | ⟨_, hh⟩
          · exact absurd hh (lt_irrefl 1)
          · exact hh
        exact hfun i j hji

lemma bc37_claw_funnelShadow_consistent (x0node bx0 : ℕ) (byv : Fin 3 → ℕ) (i : Fin 3)
    (hnode : x0node ≠ byv i) (hdistinct : ∀ j, byv j ≠ bx0) (hbyinj : Function.Injective byv) :
    ∃ up : ℕ → Prop,
      (¬ up (byv i) ∧ up bx0) ∧
      (¬ up (byv i) ∧ up x0node) ∧
      (∀ j, j ≠ i → up x0node ∧ up (byv j)) := by
  refine ⟨fun w => w ≠ byv i, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · simp
  · exact (hdistinct i).symm
  · simp
  · exact hnode
  · intro j hji
    refine ⟨hnode, ?_⟩
    exact fun he => hji (hbyinj he)

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
lemma bc37_parentFunneling_of_threeChain (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ m g : Site d} (b : Site d → Site d)
    (hx0m : x₀ ≠ m) (hx0g : x₀ ≠ g) (hmg : m ≠ g)
    (hthree : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hbm : b m ∈ box d n ∧ Connected d ω m (b m) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b m)).Infinite)
    (hbg : b g ∈ box d n ∧ Connected d ω g (b g) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b g)).Infinite)
    (hlm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
    (hsm : ¬ Connected d (removeSite m ω) (b m) x₀)
    (hlg : ¬ Connected d (removeSite g ω) (b g) (b m))
    (hsg : ¬ Connected d (removeSite g ω) (b g) m)
    (hfg : Connected d (removeSite g ω) (b x₀) m) :
    bc37_ParentFunneling ω n := by
  classical
  set dep : Site d → ℕ := fun z => if z = x₀ then 0 else if z = m then 1 else 2 with hdep
  have hdx0 : dep x₀ = 0 := by simp [hdep]
  have hdm : dep m = 1 := by simp [hdep, hx0m.symm]
  have hdg : dep g = 2 := by simp [hdep, hx0g.symm, hmg.symm]
  refine ⟨b, (fun z => toLex (dep z, 0)), (fun z => if z = g then m else x₀), ?_, ?_, ?_⟩
  · intro x hxbox htri
    rcases hthree x hxbox htri with rfl | rfl | rfl
    · exact hbx0
    · exact hbm
    · exact hbg
  · intro x hxbox htri yv hyvbox htriv hxy _
    simp only
    rcases hthree x hxbox htri with rfl | rfl | rfl <;>
      rcases hthree yv hyvbox htriv with rfl | rfl | rfl <;>
      first
      | exact absurd rfl hxy
      | (first
          | (rw [hdx0, hdm]; exact stt_lex_ne_fst (by norm_num))
          | (rw [hdx0, hdg]; exact stt_lex_ne_fst (by norm_num))
          | (rw [hdm, hdx0]; exact stt_lex_ne_fst (by norm_num))
          | (rw [hdm, hdg]; exact stt_lex_ne_fst (by norm_num))
          | (rw [hdg, hdx0]; exact stt_lex_ne_fst (by norm_num))
          | (rw [hdg, hdm]; exact stt_lex_ne_fst (by norm_num)))
  · intro x hxbox htri yv hyvbox htriv hxy _ hlt
    simp only at hlt
    rcases hthree yv hyvbox htriv with rfl | rfl | rfl
    · rcases hthree x hxbox htri with rfl | rfl | rfl
      · exact absurd rfl hxy
      · rw [hdm, hdx0] at hlt; exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
      · rw [hdg, hdx0] at hlt; exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · simp only [ite_eq_right hmg]
      rcases hthree x hxbox htri with rfl | rfl | rfl
      · exact ⟨hlm, hsm, fun hne => absurd rfl hne⟩
      · exact absurd rfl hxy
      · rw [hdg, hdm] at hlt; exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · simp only
      refine ⟨hlg, hsg, ?_⟩
      intro hxne
      rcases hthree x hxbox htri with rfl | rfl | rfl
      · exact hfg
      · exact absurd rfl hxne
      · exact absurd rfl hxy

lemma bc37_Tcount_le_boundary_of_parentFunneling (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : bc37_ParentFunneling ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bc36_Tcount_le_boundary_of_selfDownArm ω n hn (bc37_selfDownArm_of_parentFunneling ω n h)

/-! ## E. Unsatisfiability of the configuration-wide conditions -/

/-- `bc37_ArmForestRooting` for every configuration and every box of radius `n ≥ 1` is impossible
when
`d ≥ 1`: this implies the configuration-wide bound `Tcount ≤ |∂Λₙ|`, which
`tfc_not_forall_Tcount_le_boundary` refutes. -/
lemma bc37_not_forall_armForestRooting (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      bc37_ArmForestRooting ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    bc37_Tcount_le_boundary_of_armForestRooting ω n hn (h ω n hn)

/-- `bc37_ParentFunneling` for every configuration and every box of radius `n ≥ 1` is impossible
when
`d ≥ 1`: this implies the configuration-wide bound `Tcount ≤ |∂Λₙ|`, which
`tfc_not_forall_Tcount_le_boundary` refutes. -/
lemma bc37_not_forall_parentFunneling (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      bc37_ParentFunneling ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    bc37_Tcount_le_boundary_of_parentFunneling ω n hn (h ω n hn)

end StatMech.Walls

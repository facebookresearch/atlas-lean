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
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootedTreeArmSelection
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoverArmDivergence
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmDivergenceRank

/-!
# Rooted down-arm forests

Infinite arms chosen so that each later trifurcation's arm avoids the earlier ones give rooted arm
divergence, rooted tree arm selection and the trifurcation count.

## i. Overview

`bc29_RootedDownArmForest ω n rank` chooses for each trifurcation an infinite arm (after removing
all trifurcations) such that, for connected `x, y` with `rank x < rank y`, the arm of `y` is not in
the arm of `y` containing `x`. The bundled form includes a rank injective on connected
trifurcations. It gives rooted arm divergence and `bas_RootedTreeArmSelection`, hence `Tcount ≤
|∂B_n|`; it holds for a chain of three trifurcations and for claws.

No certificate of this kind can hold for every configuration: each one yields the
trifurcation-to-boundary injection `tfc_DistinctArmEnds`, and `tfc_not_forall_distinctArmEnds` shows
that this injection fails for some configuration in every dimension `d ≥ 1` (in `tfc_lineConfig`
every site is a trifurcation in the sense of `IsTrifurcation`). The certificate is useful
configuration by configuration; the deterministic counting bound is the reusable content.

## ii. Key results

- `bc29_rootedArmDivergence_of_bundled` : the bundled forest gives rooted arm divergence
- `bc29_Tcount_le_boundary_of_rootedDownArmForest` : the counting bound
- `bc29_rootedDownArmForest_of_claw` : the forest for a claw

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

lemma bc29_notSameArm_of_armSplit (ω : ConfigSpace (Sym2 (Site d)))
    {y bx by' : Site d}
    (hy_bx : Connected d ω y bx) (hne_bx : y ≠ bx)
    (hy_by : Connected d ω y by') (hne_by : y ≠ by')
    (hsplit : ¬ Connected d (removeSite y ω) by' bx) :
    ¬ fsp_sameArm ω y bx by' := by
  intro hsame
  have hwbx : Connected d (removeSite y ω) (fsp_armWitness ω y bx) bx :=
    fsp_armWitness_inArm ω hy_bx hne_bx
  have hwby : Connected d (removeSite y ω) (fsp_armWitness ω y by') by' :=
    fsp_armWitness_inArm ω hy_by hne_by
  exact hsplit ((hwby.symm.trans hsame.symm).trans hwbx)

lemma bc29_armSplit_consistent :
    ∃ (ω : ConfigSpace (Sym2 (Site 1))) (y bx by' : Site 1),
      ¬ Connected 1 (removeSite y ω) by' bx :=
  ⟨rfp_ωpath, rfp_p1, rfp_p2, rfp_p0, fun h => rfp_consistency_crossed h.symm⟩

lemma bc29_multiAncestorSplit_consistent :
    ∃ (ω : ConfigSpace (Sym2 (Site 1))) (y bx₁ bx₂ by' : Site 1),
      ¬ Connected 1 (removeSite y ω) by' bx₁ ∧ ¬ Connected 1 (removeSite y ω) by' bx₂ :=
  ⟨rfp_ωpath, rfp_p1, rfp_p0, rfp_p0, rfp_p2,
    rfp_consistency_crossed, rfp_consistency_crossed⟩

/-- A rooted down-arm forest for `B_n` and `rank`: an infinite arm (after removing all
trifurcations) for each trifurcation, with the arm of a later trifurcation avoiding the side
containing an earlier connected one. -/
def bc29_RootedDownArmForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x < rank y →
      ¬ Connected d (removeSite y ω) (b y) (b x))

lemma bc29_armDivergenceForRank_of_rootedDownArmForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (h : bc29_RootedDownArmForest ω n rank) :
    bc28_ArmDivergenceForRank ω n rank := by
  obtain ⟨b, hbdata, hsplit⟩ := h
  refine ⟨b, hbdata, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  have hsp : ¬ Connected d (removeSite y ω) (b y) (b x) :=
    hsplit x hxbox htri y hybox htriy hxy hconn hlt
  set T := tfc_trifFinset ω n with hT
  have hyT : y ∈ T := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
  have hbxnotin : b x ∉ T :=
    stac_infiniteCluster_notMem T ω (hbdata x hxbox htri).2.2
  have hbynotin : b y ∉ T :=
    stac_infiniteCluster_notMem T ω (hbdata y hybox htriy).2.2
  have hne_y_bx : y ≠ b x := fun heq => hbxnotin (heq ▸ hyT)
  have hne_y_by : y ≠ b y := fun heq => hbynotin (heq ▸ hyT)
  have hy_bx : Connected d ω y (b x) := hconn.symm.trans (hbdata x hxbox htri).2.1
  have hy_by : Connected d ω y (b y) := (hbdata y hybox htriy).2.1
  exact bc29_notSameArm_of_armSplit ω hy_bx hne_y_bx hy_by hne_y_by hsp

lemma bc29_rootedArmDivergence_of_rootedDownArmForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ)
    (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x ≠ rank y)
    (h : bc29_RootedDownArmForest ω n rank) :
    rfp_RootedArmDivergence ω n :=
  bc28_rootedArmDivergence_of_armDivergenceForRank ω n rank hinj
    (bc29_armDivergenceForRank_of_rootedDownArmForest ω n rank h)

/-- A rank injective on connected trifurcations together with a rooted down-arm forest for it. -/
def bc29_BundledRootedDownArmForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ rank : Site d → ℕ ×ₗ ℕ,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x ≠ rank y) ∧
    bc29_RootedDownArmForest ω n rank

lemma bc29_rootedArmDivergence_of_bundled (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc29_BundledRootedDownArmForest ω n) :
    rfp_RootedArmDivergence ω n := by
  obtain ⟨rank, hinj, hdatum⟩ := h
  exact bc29_rootedArmDivergence_of_rootedDownArmForest ω n rank hinj hdatum

lemma bc29_rootedTreeArmSelection_of_bundled (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc29_BundledRootedDownArmForest ω n) :
    bas_RootedTreeArmSelection ω n :=
  bc28_rootedTreeArmSelection_of_rootedArmDivergence ω n
    (bc29_rootedArmDivergence_of_bundled ω n h)

lemma bc29_Tcount_le_boundary_of_rootedDownArmForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : bc29_BundledRootedDownArmForest ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bc28_Tcount_le_boundary_of_rootedArmDivergence ω n hn
    (bc29_rootedArmDivergence_of_bundled ω n h)

lemma bc29_rootedDownArmForest_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc29_BundledRootedDownArmForest ω n := by
  refine ⟨(fun _ => toLex (0, 0)), ?_, id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)

lemma bc29_rootedDownArmForest_of_threeChain (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ m g : Site d} (b : Site d → Site d)
    (hx0box : x₀ ∈ box d n) (hmbox : m ∈ box d n) (hgbox : g ∈ box d n)
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
    bc29_BundledRootedDownArmForest ω n := by
  classical
  set dep : Site d → ℕ := fun z => if z = x₀ then 0 else if z = m then 1 else 2 with hdep
  have hdepx0 : dep x₀ = 0 := by simp [hdep]
  have hdepm : dep m = 1 := by simp [hdep, hx0m.symm]
  have hdepg : dep g = 2 := by simp [hdep, hx0g.symm, hmg.symm]
  refine ⟨(fun z => toLex (dep z, 0)), ?_, b, ?_, ?_⟩
  · intro x hxbox htri x' hx'box htri' hxx' _
    apply stt_lex_ne_fst
    rcases hthree x hxbox htri with rfl | rfl | rfl <;>
      rcases hthree x' hx'box htri' with rfl | rfl | rfl <;>
      simp only [hdepx0, hdepm, hdepg] <;>
      first | exact absurd rfl hxx' | decide
  · intro x hxbox htri
    rcases hthree x hxbox htri with rfl | rfl | rfl
    · exact hbx0
    · exact hbm
    · exact hbg
  · intro x hxbox htri y hybox htriy hxy _ hlt
    rcases hthree x hxbox htri with rfl | rfl | rfl <;>
      rcases hthree y hybox htriy with rfl | rfl | rfl
    · exact absurd rfl hxy
    · exact hsxm
    · exact hsxg
    · simp only [] at hlt; rw [hdepm, hdepx0] at hlt
      exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · exact absurd rfl hxy
    · exact hsmg
    · simp only [] at hlt; rw [hdepg, hdepx0] at hlt
      exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · simp only [] at hlt; rw [hdepg, hdepm] at hlt
      exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · exact absurd rfl hxy

lemma bc29_rootedDownArmForest_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (b : Site d → Site d)
    (hx0box : x₀ ∈ box d n)
    (hydata : ∀ i, y i ∈ box d n ∧ x₀ ≠ y i ∧ Connected d ω x₀ (y i))
    (hyinj : Function.Injective y)
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby : ∀ i, b (y i) ∈ box d n ∧ Connected d ω (y i) (b (y i)) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b (y i))).Infinite)
    (hsx0 : ∀ i, ¬ Connected d (removeSite (y i) ω) (b (y i)) (b x₀))
    (hssib : ∀ i j : Fin 3, (j : ℕ) < i →
      ¬ Connected d (removeSite (y i) ω) (b (y i)) (b (y j))) :
    bc29_BundledRootedDownArmForest ω n := by
  classical
  set rank : Site d → ℕ ×ₗ ℕ := fun z =>
    if z = x₀ then toLex (0, 0)
    else if h : ∃ i, z = y i then toLex (1, (h.choose : ℕ)) else toLex (2, 0) with hrank
  have hrx0 : rank x₀ = toLex (0, 0) := by simp only [hrank, ite_eq_left rfl]
  have hry : ∀ i, rank (y i) = toLex (1, (i : ℕ)) := by
    intro i
    have hne : y i ≠ x₀ := (hydata i).2.1.symm
    have hex : ∃ k, y i = y k := ⟨i, rfl⟩
    have hchoose : hex.choose = i := hyinj hex.choose_spec.symm
    simp only [hrank, ite_eq_right hne, dite_eq_left hex, hchoose]
  refine ⟨rank, ?_, b, ?_, ?_⟩
  · intro x hxbox htri x' hx'box htri' hxx' _
    rcases hsingle x hxbox htri with rfl | ⟨i, rfl⟩
    · rcases hsingle x' hx'box htri' with rfl | ⟨i', rfl⟩
      · exact absurd rfl hxx'
      · rw [hrx0, hry i']; exact stt_lex_ne_fst (by norm_num)
    · rcases hsingle x' hx'box htri' with rfl | ⟨i', rfl⟩
      · rw [hrx0, hry i]; exact (stt_lex_ne_fst (by norm_num)).symm
      · rw [hry i, hry i']
        have hii' : i ≠ i' := fun h => hxx' (by rw [h])
        exact stt_lex_ne_snd (fun h => hii' (Fin.ext h))
  · intro x hxbox htri
    rcases hsingle x hxbox htri with rfl | ⟨i, rfl⟩
    · exact hbx0
    · exact hby i
  · intro x hxbox htri yv hyvbox htriv hxy hconn hlt
    rcases hsingle yv hyvbox htriv with rfl | ⟨i, rfl⟩
    · rcases hsingle x hxbox htri with rfl | ⟨j, rfl⟩
      · exact absurd rfl hxy
      · rw [hry j, hrx0] at hlt; exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · rcases hsingle x hxbox htri with rfl | ⟨j, rfl⟩
      · exact hsx0 i
      · rw [hry j, hry i] at hlt
        have hji : (j : ℕ) < i := by
          rw [Prod.Lex.toLex_lt_toLex] at hlt
          rcases hlt with h | ⟨_, h⟩
          · exact absurd h (lt_irrefl 1)
          · exact h
        exact hssib i j hji

end StatMech.Walls

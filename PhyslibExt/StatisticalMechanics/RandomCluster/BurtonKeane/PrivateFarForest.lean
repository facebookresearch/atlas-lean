/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndDisjoint
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SingleCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateArmTwoTrif
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPeel
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifArms
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RenormalizedForestCount

/-!
# Private-far orders and global cut arm data

Global cut arm data give global forest arms and the trifurcation count; a private-far order is the
same as a coherent arm selector.

## i. Overview

`bc26_GlobalCutArmData ω n` chooses an infinite arm for each trifurcation such that distinct arms
are in different components after all trifurcations are removed; this gives global forest arms and
`Tcount ≤ |∂B_n|`. `bc26_PrivateFarOrder` is equivalent to `bkfl_CoherentArmSelector` and gives
private arms. Both hold for at most two trifurcations.

No certificate of this kind can hold for every configuration: each one yields the
trifurcation-to-boundary injection `tfc_DistinctArmEnds`, and `tfc_not_forall_distinctArmEnds` shows
that this injection fails for some configuration in every dimension `d ≥ 1` (in `tfc_lineConfig`
every site is a trifurcation in the sense of `IsTrifurcation`). The certificate is useful
configuration by configuration; the deterministic counting bound is the reusable content.

## ii. Key results

- `bc26_globalForestArms_of_globalCutArmData` : global cut arm data give global forest arms
- `bc26_Tcount_le_boundary_of_globalCutArmData` : the counting bound
- `bc26_privateFarOrder_iff_coherentSelector` : private-far orders are coherent selectors
- `bc26_privateFarOrder_of_twoTrif` : private-far orders with two trifurcations

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

lemma bc26_arms_globalCut_pairwise_disconnected (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) {x : Site d} (hxT : x ∈ T)
    (htri : IsTrifurcation d ω x) :
    ∃ a₁ a₂ a₃ : Site d,
      (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
      (Connected d ω x a₁ ∧ Connected d ω x a₂ ∧ Connected d ω x a₃) ∧
      ((cluster d ω a₁).Infinite ∧ (cluster d ω a₂).Infinite ∧ (cluster d ω a₃).Infinite) ∧
      (¬ Connected d (removeSites T ω) a₁ a₂ ∧
        ¬ Connected d (removeSites T ω) a₁ a₃ ∧
        ¬ Connected d (removeSites T ω) a₂ a₃) := by
  obtain ⟨a₁, a₂, a₃, hne, hconn, hinf, hsep⟩ := htri
  refine ⟨a₁, a₂, a₃, hne, hconn, hinf, ?_, ?_, ?_⟩
  · exact daep2_globalCut_disconnected_of_singleCut T ω hxT hsep.1
  · exact daep2_globalCut_disconnected_of_singleCut T ω hxT hsep.2.1
  · exact daep2_globalCut_disconnected_of_singleCut T ω hxT hsep.2.2

lemma bc26_avoiding_arm_of_trif (ω : ConfigSpace (Sym2 (Site d)))
    {x : Site d} (htri : IsTrifurcation d ω x) (y : Site d) :
    ∃ a : Site d, Connected d ω x a ∧ (cluster d ω a).Infinite ∧
      ¬ bkfl_inArm ω x a y := by
  obtain ⟨a₁, a₂, a₃, _hne, hconn, hinf, hsep⟩ := htri
  rcases StatMech.Percolation.daep2_two_branches_avoid ω hsep.1 hsep.2.1 hsep.2.2 y with
    ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h2, _⟩
  · exact ⟨a₁, hconn.1, hinf.1, h1⟩
  · exact ⟨a₁, hconn.1, hinf.1, h1⟩
  · exact ⟨a₂, hconn.2.1, hinf.2.1, h2⟩

/-- Global cut arm data for `B_n`: each trifurcation has an arm site whose cluster stays infinite
after all trifurcations are removed, and the arm sites of distinct trifurcations lie in
different components of that configuration. -/
def bc26_GlobalCutArmData (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → ¬ aed_sameGlobalComponent (tfc_trifFinset ω n) ω (b x) (b y))

lemma bc26_globalForestArms_of_globalCutArmData (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc26_GlobalCutArmData ω n) : aed_GlobalForestArms ω n :=
  h

lemma bc26_Tcount_le_boundary_of_globalCutArmData (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : bc26_GlobalCutArmData ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  aed_Tcount_le_boundary_of_globalForestArms ω n hn
    (bc26_globalForestArms_of_globalCutArmData ω n h)

/-- A private-far order for `B_n`: arm data for every trifurcation, private with respect to every
other connected trifurcation. -/
def bc26_PrivateFarOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → bkfl_ArmData ω n b x) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → bkfl_PrivateFar ω b x y)

lemma bc26_privateFarOrder_iff_coherentSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc26_PrivateFarOrder ω n ↔ bkfl_CoherentArmSelector ω n := Iff.rfl

lemma bc26_privateArm_of_privateFarOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc26_PrivateFarOrder ω n) : daepf_PrivateArm ω n :=
  bkfl_privateArm_of_coherentSelector ω n h

lemma bc26_count_of_privateFarOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : bc26_PrivateFarOrder ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  daepf_Tcount_le_boundary_of_privateArm ω n hn
    (bc26_privateArm_of_privateFarOrder ω n h)

lemma bc26_coarseTrif_arms_cutInfinite {ω : ConfigSpace (Sym2 (Site d))}
    (h : IsCoarseTrifurcation d 0 ω) :
    ∃ a₁ a₂ a₃ : Site d,
      (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
      (Connected d ω (0 : Site d) a₁ ∧ Connected d ω (0 : Site d) a₂ ∧
        Connected d ω (0 : Site d) a₃) ∧
      ((cluster d (removeSite (0 : Site d) ω) a₁).Infinite ∧
        (cluster d (removeSite (0 : Site d) ω) a₂).Infinite ∧
        (cluster d (removeSite (0 : Site d) ω) a₃).Infinite) ∧
      (¬ Connected d (removeSite (0 : Site d) ω) a₁ a₂ ∧
        ¬ Connected d (removeSite (0 : Site d) ω) a₁ a₃ ∧
        ¬ Connected d (removeSite (0 : Site d) ω) a₂ a₃) := by
  obtain ⟨a₁, a₂, a₃, b₁, b₂, b₃, hne, hbox, _hadj, hconn, hinf, hsep⟩ := h
  have hbox0 : ∀ {b : Site d}, b ∈ box d 0 → b = (0 : Site d) := by
    intro b hb; rw [bc24_box_zero] at hb; simpa using hb
  have hb₁0 : b₁ = (0 : Site d) := hbox0 hbox.1
  have hb₂0 : b₂ = (0 : Site d) := hbox0 hbox.2.1
  have hb₃0 : b₃ = (0 : Site d) := hbox0 hbox.2.2
  have hbridge := bc24_removeSites_box_zero (d := d) ω
  rw [hbridge] at hinf hsep
  refine ⟨a₁, a₂, a₃, hne, ?_, hinf, hsep⟩
  exact ⟨(hb₁0 ▸ hconn.1).symm, (hb₂0 ▸ hconn.2.1).symm, (hb₃0 ▸ hconn.2.2).symm⟩

lemma bc26_globalForestArms_of_uniqueTrif_cutArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    aed_GlobalForestArms ω n :=
  aed_globalForestArms_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq

lemma bc26_privateFarOrder_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc26_PrivateFarOrder ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri _ _ _ _ _; exact absurd htri (hno x hxbox)

lemma bc26_privateFarOrder_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    bc26_PrivateFarOrder ω n := by
  classical
  have hT : tfc_trifFinset ω n = {x₀} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨tfc_mem_trifFinset.mpr ⟨hx0box, htri0⟩, ?_⟩
    intro y hy; rw [tfc_mem_trifFinset] at hy; exact huniq y hy.1 hy.2
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

lemma bc26_privateFarOrder_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d)
    (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hdata_x : bkfl_ArmData ω n b x₀) (hdata_y : bkfl_ArmData ω n b y₀)
    (hpf_xy : bkfl_PrivateFar ω b x₀ y₀) (hpf_yx : bkfl_PrivateFar ω b y₀ x₀) :
    bc26_PrivateFarOrder ω n := by
  classical
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hdata_x
    · exact hdata_y
  · intro x hxbox htri y hybox htriy hxy _
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo y hybox htriy with rfl | rfl
      · exact absurd rfl hxy
      · exact hpf_xy
    · rcases htwo y hybox htriy with rfl | rfl
      · exact hpf_yx
      · exact absurd rfl hxy

end StatMech.Walls

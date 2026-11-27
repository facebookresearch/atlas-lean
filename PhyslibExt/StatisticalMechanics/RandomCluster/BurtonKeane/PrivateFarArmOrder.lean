/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndDisjoint
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SingleCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateArmTwoTrif
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPeel
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DivergentArmOrder
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClawDivergentArmOrder
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootedTreeArmSelection
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateFarForest

/-!
# Claws exclude private-far arm orders

In a claw configuration every private-far arm of the centre meets a child, so neither a private-far
order nor a coherent arm selector exists.

## i. Overview

In a claw (a trifurcation `x₀` connected to three trifurcations `y i`, with no others), each arm of
`x₀` leads to one of the `y i`, so a private-far arm of `x₀` must meet a child. Hence claw
configurations have neither `bc26_PrivateFarOrder` nor `bkfl_CoherentArmSelector`; these
certificates fail for some configurations.

## ii. Key results

- `bc27_privateFar_forces_arm_meets_child` : private-far arms of the centre meet a child
- `bc27_not_privateFarOrder_of_claw` : claws exclude private-far orders
- `bc27_not_coherentSelector_of_claw` : claws exclude coherent arm selectors

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

lemma bc27_privateFar_forces_arm_meets_child (ω : ConfigSpace (Sym2 (Site d)))
    {x₀ bx₀ : Site d} {y : Fin 3 → Site d} {lx : Site d → Fin 3}
    (hlxf : ∀ u v, Connected d ω x₀ u → x₀ ≠ u → Connected d ω x₀ v → x₀ ≠ v →
      (lx u = lx v ↔ fsp_sameArm ω x₀ u v))
    (hydown : ∀ i, lx (y i) = i)
    (hydata : ∀ i, x₀ ≠ y i ∧ Connected d ω x₀ (y i))
    (hbxconn : Connected d ω x₀ bx₀) (hbxne : x₀ ≠ bx₀) :
    bkfl_inArm ω x₀ bx₀ (y (lx bx₀)) := by
  set i := lx bx₀ with hi
  have hcoll : lx bx₀ = lx (y i) := by rw [hydown i]
  have hsame : fsp_sameArm ω x₀ bx₀ (y i) :=
    (hlxf bx₀ (y i) hbxconn hbxne (hydata i).2 (hydata i).1).mp hcoll
  have hw1 : Connected d (removeSite x₀ ω) (fsp_armWitness ω x₀ bx₀) bx₀ :=
    fsp_armWitness_inArm ω hbxconn hbxne
  have hw2 : Connected d (removeSite x₀ ω) (fsp_armWitness ω x₀ (y i)) (y i) :=
    fsp_armWitness_inArm ω (hydata i).2 (hydata i).1
  exact hw1.symm.trans (hsame.trans hw2)

lemma bc27_not_privateFarOrder_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hclaw : stac_ClawConfig ω n) : ¬ bc26_PrivateFarOrder ω n := by
  classical
  obtain ⟨x₀, y, lx, ly, ⟨hx0box, htri0⟩, hydata, hyinj, hlxf, hlyf, hydown, hGstar⟩ := hclaw
  rintro ⟨b, hbdata, hpair⟩
  set T := tfc_trifFinset ω n with hT
  obtain ⟨_, hbx0conn, hbx0inf⟩ := hbdata x₀ hx0box htri0
  have hbx0notin : b x₀ ∉ T := stac_infiniteCluster_notMem T ω hbx0inf
  have hx0T : x₀ ∈ T := tfc_mem_trifFinset.mpr ⟨hx0box, htri0⟩
  have hne_bx0 : x₀ ≠ b x₀ := fun h => hbx0notin (h ▸ hx0T)
  set i : Fin 3 := lx (b x₀) with hi
  have hmeet : bkfl_inArm ω x₀ (b x₀) (y i) :=
    bc27_privateFar_forces_arm_meets_child ω hlxf hydown
      (fun j => ⟨(hydata j).2.2.1, (hydata j).2.2.2⟩) hbx0conn hne_bx0
  have hyibox : y i ∈ box d n := (hydata i).1
  have hyitri : IsTrifurcation d ω (y i) := (hydata i).2.1
  have hxy : x₀ ≠ y i := (hydata i).2.2.1
  have hconn : Connected d ω x₀ (y i) := (hydata i).2.2.2
  obtain ⟨hpriv, _hfar⟩ := hpair x₀ hx0box htri0 (y i) hyibox hyitri hxy hconn
  exact hpriv hmeet

lemma bc27_not_coherentSelector_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hclaw : stac_ClawConfig ω n) : ¬ bkfl_CoherentArmSelector ω n := by
  intro h
  exact bc27_not_privateFarOrder_of_claw ω n hclaw
    ((bc26_privateFarOrder_iff_coherentSelector ω n).mpr h)

end StatMech.Walls

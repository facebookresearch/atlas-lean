/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Mathlib
import Code.Percolation.ArmEndDisjointClose
import Code.Percolation.DisjointArmEndsProve2
import Code.Percolation.DisjointArmEndsFinal
import Code.Percolation.BKForestLib
import Code.Percolation.ForestSelectorProve
import Code.Percolation.SpanningTreeArmClose
import Code.Percolation.BKArmSelectorClose
import Code.Walls.bc26forest

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

















theorem bc27_privateFar_forces_arm_meets_child (ω : ConfigSpace (Sym2 (Site d)))
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



















theorem bc27_not_privateFarOrder_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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





theorem bc27_privateFarOrder_not_universal (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hclaw : stac_ClawConfig ω n) :
    ¬ bc26_PrivateFarOrder ω n :=
  bc27_not_privateFarOrder_of_claw ω n hclaw











theorem bc27_not_coherentSelector_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hclaw : stac_ClawConfig ω n) : ¬ bkfl_CoherentArmSelector ω n := by
  intro h
  exact bc27_not_privateFarOrder_of_claw ω n hclaw
    ((bc26_privateFarOrder_iff_coherentSelector ω n).mpr h)














theorem bc27_globalForestArms_of_rootedTreeArmSelection (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : bas_RootedTreeArmSelection ω n) : aed_GlobalForestArms ω n :=
  bas_globalForestArms_of_rootedTreeArmSelection ω n h




theorem bc27_count_of_rootedTreeArmSelection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : bas_RootedTreeArmSelection ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bas_Tcount_le_boundary_of_rootedTreeArmSelection ω n hn h










theorem bc27_burton_keane_bernoulli_of_rootedTreeArmSelection (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      bas_RootedTreeArmSelection ω n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bas_burton_keane_bernoulli_of_rootedTreeArmSelection hd p hp1 hp0 hres htrif













theorem bc27_rootedTreeArmSelection_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (lx : Site d → Fin 3) (ly : Fin 3 → Site d → Fin 3)
    (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧
      Connected d ω x₀ (y i))
    (hyinj : Function.Injective y)
    (hlxf : ∀ u v, Connected d ω x₀ u → x₀ ≠ u → Connected d ω x₀ v → x₀ ≠ v →
      (lx u = lx v ↔ fsp_sameArm ω x₀ u v))
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
    bas_RootedTreeArmSelection ω n :=
  bas_rootedTreeArmSelection_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlxf hlyf hGstar
    hsingle b hbdata hcy hcx hcentral











theorem bc27_privateFarOrder_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc26_PrivateFarOrder ω n :=
  bc26_privateFarOrder_of_noTrif ω n hno


theorem bc27_privateFarOrder_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    bc26_PrivateFarOrder ω n :=
  bc26_privateFarOrder_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq





theorem bc27_privateFarOrder_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d)
    (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hdata_x : bkfl_ArmData ω n b x₀) (hdata_y : bkfl_ArmData ω n b y₀)
    (hpf_xy : bkfl_PrivateFar ω b x₀ y₀) (hpf_yx : bkfl_PrivateFar ω b y₀ x₀) :
    bc26_PrivateFarOrder ω n :=
  bc26_privateFarOrder_of_twoTrif ω n b hx0y0 htwo hdata_x hdata_y hpf_xy hpf_yx

end StatMech.Walls

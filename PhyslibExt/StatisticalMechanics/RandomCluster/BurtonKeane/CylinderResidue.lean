/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClosedCorridors
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MeasurableDependence
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrecursorDecoupling
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FineTrifRoute

/-!
# Cylinder patterns and the arm residue

Cylinder events are measurable and depend only on their edges, so they are independent of extension
events; the arm residue gives precursors of positive probability, the route and uniqueness on `ℤ²`.

## i. Overview

`cylinder I {η₀}` depends only on the edges of `I` and is measurable. It is independent of an
extension event depending on the other edges, so for `0 < p < 1` their intersection, which produces
a precursor, has positive probability. `bcl_ArmResidue p hp1` asks every box with three clusters
meeting it with positive probability for such a pattern and extension event. It gives the route and
uniqueness on `ℤ²`.

The uniqueness theorems here assume the arm residue, which is not proved in this module.

## ii. Key results

- `bcl_precursorPos` : a precursor of positive probability.
- `bcl_bk` : uniqueness from the arm residue.

## iii. Table of contents

- A. Cylinder events
- B. The arm residue

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), Section 8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech.Walls

set_option maxRecDepth 4000

/-! ## A. Cylinder events -/

lemma bcl_cylinder_dependsOn (I : Finset (Sym2 (Site 2))) (η₀ : ConfigSpace ↥I) :
    DependsOn (cylinder I ({η₀} : Set (ConfigSpace ↥I))) (↑I : Set (Sym2 (Site 2))) := by
  intro ω ω' hag
  simp only [MeasureTheory.mem_cylinder, Set.mem_singleton_iff]
  have hres : Finset.restrict I ω = Finset.restrict I ω' := by
    funext i
    exact (hag i.1 (Finset.mem_coe.mpr i.2)).symm
  rw [hres]

lemma bcl_cylinder_measurable (I : Finset (Sym2 (Site 2))) (η₀ : ConfigSpace ↥I) :
    MeasurableSet ((cylinder I ({η₀} : Set (ConfigSpace ↥I))) :
      Set (ConfigSpace (Sym2 (Site 2)))) := by
  have hrestr : Measurable (fun ω : ConfigSpace (Sym2 (Site 2)) => Finset.restrict I ω) :=
    measurable_pi_iff.mpr (fun i => measurable_pi_apply (i : Sym2 (Site 2)))
  exact hrestr (MeasurableSet.of_discrete)

lemma bcl_hindep (p : ℝ≥0) (hp1 : p ≤ 1)
    (I : Finset (Sym2 (Site 2))) (a₁ a₂ a₃ x₁ x₂ x₃ : Site 2) (η₀ : ConfigSpace ↥I)
    (hExtMeas : MeasurableSet (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃)) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        (cylinder I ({η₀} : Set (ConfigSpace ↥I)) ∩ bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃)
      = bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          (cylinder I ({η₀} : Set (ConfigSpace ↥I)))
        * bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
            (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃) :=
  bfc2_indep_finite_cofinite p hp1 I
    (bcl_cylinder_measurable I η₀) hExtMeas
    (bcl_cylinder_dependsOn I η₀)
    (bpt2_Ext_dependsOn I a₁ a₂ a₃ x₁ x₂ x₃)

lemma bcl_precursorPos (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (I : Finset (Sym2 (Site 2))) (a₁ a₂ a₃ x₁ x₂ x₃ : Site 2) (η₀ : ConfigSpace ↥I)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
      (hypercubicLattice 2).Adj 0 a₃)
    (hcorr : ∀ ω ∈ cylinder I ({η₀} : Set (ConfigSpace ↥I)),
      Connected 2 (removeSite 0 ω) a₁ x₁ ∧ Connected 2 (removeSite 0 ω) a₂ x₂ ∧
        Connected 2 (removeSite 0 ω) a₃ x₃)
    (hExtMeas : MeasurableSet (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃))
    (hXpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃)) :
    0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      (NeighborTrifPrecursor 2 a₁ a₂ a₃) :=
  bpt2_precursorPos_of_residues p hp1 hp0 hplt I a₁ a₂ a₃ x₁ x₂ x₃ η₀ hne hadj hcorr
    (bcl_hindep p hp1 I a₁ a₂ a₃ x₁ x₂ x₃ η₀ hExtMeas) hXpos

/-! ## B. The arm residue -/

/-- Arm residue: every box with three infinite clusters meeting it with positive probability has a
cylinder pattern on a finite edge set and an extension event of positive probability producing a
neighbour precursor. -/
def bcl_ArmResidue (p : ℝ≥0) (hp1 : p ≤ 1) : Prop :=
  ∀ n : ℕ,
    0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n) →
      ∃ (I : Finset (Sym2 (Site 2))) (a₁ a₂ a₃ x₁ x₂ x₃ : Site 2) (η₀ : ConfigSpace ↥I),
        (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
        ((hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
          (hypercubicLattice 2).Adj 0 a₃) ∧
        (∀ ω ∈ cylinder I ({η₀} : Set (ConfigSpace ↥I)),
          Connected 2 (removeSite 0 ω) a₁ x₁ ∧ Connected 2 (removeSite 0 ω) a₂ x₂ ∧
            Connected 2 (removeSite 0 ω) a₃ x₃) ∧
        MeasurableSet (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃) ∧
        0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃)

lemma bcl_hroute_of_residue (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (hres : bcl_ArmResidue p hp1) :
    ∀ n : ℕ,
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n) →
        ∃ a₁ a₂ a₃ : Site 2,
          0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
            (NeighborTrifPrecursor 2 a₁ a₂ a₃) := by
  intro n htop
  obtain ⟨I, a₁, a₂, a₃, x₁, x₂, x₃, η₀, hne, hadj, hcorr, hExtMeas, hXpos⟩ := hres n htop
  exact ⟨a₁, a₂, a₃,
    bcl_precursorPos p hp1 hp0 hplt I a₁ a₂ a₃ x₁ x₂ x₃ η₀ hne hadj hcorr hExtMeas hXpos⟩

lemma bcl_bk (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (hres : bcl_ArmResidue p hp1) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {ω | numInfiniteClusters 2 ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {ω | numInfiniteClusters 2 ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          {ω | numInfiniteClusters 2 ω ≤ 1} = 1 :=
  bfx_bk_of_route (by norm_num) p hp1 hp0 (bcl_hroute_of_residue p hp1 hp0 hplt hres)

lemma bcl_bk_atLeastTwo (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (hres : bcl_ArmResidue p hp1) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  (bcl_bk p hp1 hp0 hplt hres).2.1

end StatMech.Walls

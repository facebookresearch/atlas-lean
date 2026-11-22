/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.PressureBCIndep
public import PhyslibExt.CondensedMatter.IsingModel.PressureConvex

/-!
# Summary of the pressure results

Existence, value and convexity of the pressure, and boundary-condition independence of box
pressures.

## i. Overview

Collects the results of `Pressure`, `PressureConvex` and `PressureBCIndep`: for a finite graph the
pressure of independent copies exists, equals `log Z` and is convex in `β` and `h`; box `log Z` with
plus boundary condition is convex in `β` and `h`, and plus and free box pressures have the same
limit under a surface-to-volume hypothesis.

## ii. Key results

- `StatMech.Ising.pressure_full` : the finite-graph pressure
- `StatMech.Ising.boxPressure_full` : box pressures
- `StatMech.Ising.boxPressure_plus_free_same_limit` : equal limits of plus and free box pressures

## iii. Table of contents

- A. Summary

## iv. References

- D. Ruelle, *Statistical Mechanics: Rigorous Results*, Benjamin (1969)
-/

@[expose] public section

open scoped BigOperators
open Finset Filter Topology

namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}

lemma logFvZ_convexOn_beta (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (h : ℝ) :
    ConvexOn ℝ Set.univ (fun β : ℝ => Real.log (fvZ η n B β h)) := by
  have hconv := cumulant_convexOn (ι := {x // x ∈ box d n} → Bool)
    (fun τ => - fvEnergy η n B h τ) (fun _ => 0)
  refine hconv.congr ?_
  intro β _
  simp only
  congr 1
  unfold fvZ fvWeight
  apply Finset.sum_congr rfl
  intro τ _
  congr 1
  ring

lemma logFvZ_convexOn_field (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β : ℝ) :
    ConvexOn ℝ Set.univ (fun h : ℝ => Real.log (fvZ η n B β h)) := by
  have hconv := cumulant_convexOn (ι := {x // x ∈ box d n} → Bool)
    (fun τ => β * ∑ x ∈ boxFinset d n, spin (glue η τ) x)
    (fun τ => β * ∑ e ∈ B, bond (glue η τ) e)
  refine hconv.congr ?_
  intro h _
  simp only
  congr 1
  unfold fvZ fvWeight fvEnergy
  apply Finset.sum_congr rfl
  intro τ _
  congr 1
  ring

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Summary -/

lemma pressure_full (β h : ℝ) :
    Tendsto (fun n => logZSeq β (hamiltonian G h) n / n) atTop
        (𝓝 (pressure β (hamiltonian G h)))
      ∧ pressure β (hamiltonian G h) = Real.log (isingZ G β h)
      ∧ ConvexOn ℝ Set.univ (fun β' : ℝ => Real.log (isingZ G β' h))
      ∧ ConvexOn ℝ Set.univ (fun h' : ℝ => Real.log (isingZ G β h')) :=
  ⟨ising_pressure_exists G β h,
   ising_pressure_eq G β h,
   isingLogZ_convexOn_beta G h,
   isingLogZ_convexOn_field G β⟩

lemma boxPressure_full (n : ℕ) (β h : ℝ)
    (hratio : Tendsto
      (fun m => (|β| * (((bondFinsetTouch d m) \ (bondFinsetInternal d m)).card : ℝ))
        / ((boxFinset d m).card : ℝ)) atTop (𝓝 0)) :
    ConvexOn ℝ Set.univ
        (fun β' : ℝ => Real.log (fvZ (plusField d) n (bondFinsetTouch d n) β' h))
      ∧ ConvexOn ℝ Set.univ
        (fun h' : ℝ => Real.log (fvZ (plusField d) n (bondFinsetTouch d n) β h'))
      ∧ Tendsto (fun m =>
            Real.log (fvZ (plusField d) m (bondFinsetTouch d m) β h)
              / ((boxFinset d m).card : ℝ)
          - Real.log (fvZ (minusField d) m (bondFinsetInternal d m) β h)
              / ((boxFinset d m).card : ℝ))
          atTop (𝓝 0) :=
  ⟨logFvZ_convexOn_beta (plusField d) n (bondFinsetTouch d n) h,
   logFvZ_convexOn_field (plusField d) n (bondFinsetTouch d n) β,
   plus_free_pressure_indep β h hratio⟩

lemma boxPressure_plus_free_same_limit (β h p : ℝ)
    (hratio : Tendsto
      (fun m => (|β| * (((bondFinsetTouch d m) \ (bondFinsetInternal d m)).card : ℝ))
        / ((boxFinset d m).card : ℝ)) atTop (𝓝 0))
    (hplus : Tendsto
      (fun m => Real.log (fvZ (plusField d) m (bondFinsetTouch d m) β h)
        / ((boxFinset d m).card : ℝ)) atTop (𝓝 p)) :
    Tendsto
      (fun m => Real.log (fvZ (minusField d) m (bondFinsetInternal d m) β h)
        / ((boxFinset d m).card : ℝ)) atTop (𝓝 p) := by
  have hdiff := plus_free_pressure_indep (d := d) β h hratio
  have hcomb := hplus.sub hdiff
  simp only [sub_zero] at hcomb
  refine hcomb.congr ?_
  intro m
  ring

end Ising

end StatMech

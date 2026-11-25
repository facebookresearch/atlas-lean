/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Classical.TwoLocusSelection
public import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt.Biology.PopulationGenetics
open MathlibExt.Biology.PopulationGenetics.Classical.TwoLocusSelection

namespace MathlibExtTest.Biology.PopulationGenetics.Classical.TwoLocusSelection

/-- First-locus allele frequencies `(1/3, 2/3)` in `(true, false)` order. -/
noncomputable def pEx : Bool → ℝ := fun b => if b then 1 / 3 else 2 / 3

/-- Second-locus allele frequencies `(1/4, 3/4)` in `(true, false)` order. -/
noncomputable def qEx : Bool → ℝ := fun b => if b then 1 / 4 else 3 / 4

/-- First-locus fitnesses `(3, 1)` in `(true, false)` order. -/
def aEx : Bool → ℝ := fun b => if b then 3 else 1

/-- Second-locus fitnesses `(2, 1)` in `(true, false)` order. -/
def bEx : Bool → ℝ := fun b => if b then 2 else 1

/-- Product haplotype frequencies for the example. -/
noncomputable def xEx : Bool × Bool → ℝ := fun g => pEx g.1 * qEx g.2

/-- Multiplicative haplotype fitnesses for the example. -/
noncomputable def wEx : Bool × Bool → ℝ := fun g => aEx g.1 * bEx g.2

/-- At `r = 1/2`, the `AB` frequency after selection and recombination is
`(3/5) * (2/5) = 6/25`. -/
example :
    Linkage.recombine (1 / 2) (Selection.select xEx wEx) (true, true) = 6 / 25 := by
  rw [recombine_select_of_mul (r := 1 / 2) (x := xEx) (w := wEx)
    (p := pEx) (q := qEx) (a := aEx) (b := bEx) (fun _ => rfl) (fun _ => rfl)]
  norm_num [Selection.select, Selection.meanFitness, pEx, qEx, aEx, bEx,
    Fintype.sum_bool]

/-- The example output has zero linkage disequilibrium. -/
example :
    Linkage.linkageDiseq
        (Linkage.recombine (1 / 2) (Selection.select xEx wEx)) = 0 :=
  linkageDiseq_recombine_select_of_mul (r := 1 / 2) (fun _ => rfl) (fun _ => rfl)

open Linkage Selection

private def frequencies (xAB xAb xaB xab : ℝ) : Bool × Bool → ℝ
  | (true, true) => xAB
  | (true, false) => xAb
  | (false, true) => xaB
  | (false, false) => xab

private def additiveFitness : Bool × Bool → ℝ := frequencies 3 2 2 1

private theorem additiveFitness_pos (g : Bool × Bool) : 0 < additiveFitness g := by
  obtain ⟨a, b⟩ := g
  cases a <;> cases b <;> norm_num [additiveFitness, frequencies]

-- Asymmetric, initially associated haplotypes: selection changes the ratio from 6 to 9/2.
example :
    let x := frequencies (2 / 5) (1 / 5) (1 / 10) (3 / 10)
    let y := select x additiveFitness
    linkageDiseq y = 4 / 63 ∧
      y (true, true) * y (false, false) / (y (true, false) * y (false, true)) = 9 / 2 := by
  let x := frequencies (2 / 5) (1 / 5) (1 / 10) (3 / 10)
  have hx (g : Bool × Bool) : 0 ≤ x g := by
    obtain ⟨a, b⟩ := g
    cases a <;> cases b <;> norm_num [x, frequencies]
  have hsum : ∑ g, x g = 1 := by norm_num [sum_four, x, frequencies]
  have hden : 0 < x (true, false) * x (false, true) := by norm_num [x, frequencies]
  have h := haploid_selection_crossproduct_ratio hx hsum additiveFitness_pos
  refine ⟨?_, ?_⟩
  · rw [h.1]
    norm_num [meanFitness, sum_four, x, additiveFitness, frequencies]
  · rw [(h.2.1 hden).2]
    norm_num [x, additiveFitness, frequencies]

-- Starting at equilibrium, the same additive example has multiplicative epistasis -1/4
-- and creates strictly negative disequilibrium (not simply a smaller positive value).
example :
    let x : Bool × Bool → ℝ := fun _ => 1 / 4
    linkageDiseq (select x additiveFitness) < 0 := by
  let x : Bool × Bool → ℝ := fun _ => 1 / 4
  have hx (g : Bool × Bool) : 0 ≤ x g := by norm_num [x]
  have hsum : ∑ g, x g = 1 := by norm_num [sum_four, x]
  have h := haploid_selection_crossproduct_ratio hx hsum additiveFitness_pos
  have heq : linkageDiseq x = 0 := by norm_num [linkageDiseq, x]
  have hp : alleleFreqFst x true = 1 / 2 := by norm_num [alleleFreqFst, x]
  have hq : alleleFreqSnd x true = 1 / 2 := by norm_num [alleleFreqSnd, x]
  have hep := h.2.2.2 1 1 (-1 / 4) (by norm_num [additiveFitness, frequencies])
    (by norm_num [additiveFitness, frequencies]) (by norm_num [additiveFitness, frequencies])
    (by norm_num [additiveFitness, frequencies])
  exact (hep.2 (by norm_num [additiveFitness, frequencies])).2 (by norm_num) heq
    (by rw [hp]; norm_num) (by rw [hp]; norm_num) (by rw [hq]; norm_num) (by rw [hq]; norm_num)

-- Nonmultiplicative fitnesses do not create LD when the first locus is fixed for `A`.
example :
    linkageDiseq (select (frequencies (1 / 3) (2 / 3) 0 0) additiveFitness) = 0 := by
  let x := frequencies (1 / 3) (2 / 3) 0 0
  have hx (g : Bool × Bool) : 0 ≤ x g := by
    obtain ⟨a, b⟩ := g
    cases a <;> cases b <;> norm_num [x, frequencies]
  have hsum : ∑ g, x g = 1 := by norm_num [sum_four, x, frequencies]
  have heq : linkageDiseq x = 0 := by norm_num [linkageDiseq, x, frequencies]
  have h := (haploid_selection_crossproduct_ratio hx hsum additiveFitness_pos).2.2.1 heq
  apply h.2.2.2.1.mpr
  exact Or.inr (Or.inr (Or.inl (by norm_num [alleleFreqFst, x, frequencies])))

end MathlibExtTest.Biology.PopulationGenetics.Classical.TwoLocusSelection

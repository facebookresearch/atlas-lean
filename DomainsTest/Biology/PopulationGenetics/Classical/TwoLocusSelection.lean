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

end MathlibExtTest.Biology.PopulationGenetics.Classical.TwoLocusSelection

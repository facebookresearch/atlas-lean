/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.GKS2

/-!
# The duplicated-variable factor of the GHS inequality

The GKS II weight factor `1 - σ_B` is sign-definite, but the corresponding GHS factor at three
distinct sites is not.

## i. Overview

In Ginibre's proof of the second Griffiths inequality the extra factor `1 - σ_B(q)` of the
duplicated variable is nonnegative for every configuration `q`. For the Griffiths–Hurst–Sherman
inequality the analogous factor at three sites `o, x, y` is `1 - σ_x σ_y - σ_o σ_y - σ_o σ_x`, which
takes both signs when `o ≠ x ≠ y`. So the GHS inequality does not follow from the two-copy argument
alone; it needs the four-copy (or random-current) argument.

## ii. Key results

- `StatMech.Ising.ghsQFactor` : the three-site factor `1 - σ_xσ_y - σ_oσ_y - σ_oσ_x`
- `StatMech.Ising.ghsQFactor_not_signDefinite` : the three-site factor takes both signs
- `StatMech.Ising.dup_signDefinite_iff_single` : the GKS II factor is sign-definite and the GHS
  factor is not

## iii. Table of contents

- A. The three-site factor

## iv. References

- R. B. Griffiths, C. A. Hurst and S. Sherman, *Concavity of magnetization of an Ising ferromagnet
  in a positive external field*, J. Math. Phys. 11 (1970) 790–795
- J. Ginibre, *General formulation of Griffiths' inequalities*, Comm. Math. Phys. 16 (1970) 310–328
-/

@[expose] public section

open scoped BigOperators symmDiff
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. The three-site factor -/

/-- The three-site duplicated-variable factor `1 - σ_x σ_y - σ_o σ_y - σ_o σ_x` of the configuration
`q`. -/
noncomputable def ghsQFactor (q : ConfigSpace V) (o x y : V) : ℝ :=
  1 - spin q x * spin q y - spin q o * spin q y - spin q o * spin q x

omit [Fintype V] [DecidableEq V] in
lemma ghsQFactor_eq (q : ConfigSpace V) (o x y : V) :
    ghsQFactor q o x y
      = 1 - spin q x * spin q y - spin q o * spin q y - spin q o * spin q x := rfl

omit [Fintype V] [DecidableEq V] in
lemma ghsQFactor_const_one (o x y : V) :
    ghsQFactor (fun _ => true) o x y = -2 := by
  unfold ghsQFactor spin
  norm_num

omit [Fintype V] in
lemma ghsQFactor_single_flip {o x y : V} (hox : o ≠ x) (hxy : x ≠ y) :
    ghsQFactor (fun z => decide (z ≠ x)) o x y = 2 := by
  unfold ghsQFactor spin
  have ho : ((fun z => decide (z ≠ x)) o = true) := by simp [hox]
  have hx : ¬ ((fun z => decide (z ≠ x)) x = true) := by simp
  have hy : ((fun z => decide (z ≠ x)) y = true) := by simp [Ne.symm hxy]
  rw [ite_eq_left ho, ite_eq_right hx, ite_eq_left hy]
  norm_num

omit [Fintype V] in
lemma ghsQFactor_not_signDefinite {o x y : V} (hox : o ≠ x) (hxy : x ≠ y) :
    (∃ q : ConfigSpace V, ghsQFactor q o x y < 0)
      ∧ (∃ q : ConfigSpace V, 0 < ghsQFactor q o x y) := by
  refine ⟨⟨fun _ => true, ?_⟩, ⟨fun z => decide (z ≠ x), ?_⟩⟩
  · rw [ghsQFactor_const_one]; norm_num
  · rw [ghsQFactor_single_flip hox hxy]; norm_num

omit [Fintype V] in
lemma dup_signDefinite_iff_single (B : Finset V) {o x y : V}
    (hox : o ≠ x) (hxy : x ≠ y) :
    (∀ q : ConfigSpace V, 0 ≤ 1 - spinProd B q)
      ∧ ¬ (∀ q : ConfigSpace V, 0 ≤ ghsQFactor q o x y) := by
  refine ⟨fun q => one_sub_spinProd_nonneg B q, ?_⟩
  intro hall
  obtain ⟨⟨q, hq⟩, _⟩ := ghsQFactor_not_signDefinite (o := o) (x := x) (y := y) hox hxy
  exact absurd (hall q) (not_le.mpr hq)

end Ising

end StatMech

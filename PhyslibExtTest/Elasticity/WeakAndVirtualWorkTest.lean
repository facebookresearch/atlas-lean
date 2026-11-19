/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Elasticity.WeakAndVirtualWork
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Elasticity.WeakAndVirtualWork`

* a constant-rigidity bar under a nonzero uniform load: the weak solution has the classical
  midspan displacement;
* a positive two-valued rigidity: the existence theorem applies;
* inadmissible data: zero rigidity under a unit load, and a traction end.
-/

@[expose] public section

namespace PhyslibExtTest.Elasticity.WeakAndVirtualWork

open MeasureTheory _root_.Elasticity.WeakAndVirtualWork _root_.Elasticity.PrismaticMembers

/-! ## A. Constant rigidity -/

-- Nonzero fixture `EA = 2`, `L = 3`, `q = 4`: a weak solution exists and its midspan
-- displacement is the classical `q L ^ 2 / (8 EA) = 9 / 4`.
example :
    ∃ u : WeakH10On 3, IsWeakBarSolution (fun _ => 2) (fun _ => 4) u ∧ u.toFun (3 / 2) = 9 / 4 := by
  obtain ⟨u, hu, -⟩ := weakBar_exists_unique (L := 3) (EA := fun _ => 2) (q := fun _ => 4)
    (EAmin := 2) (EAmax := 2) (by norm_num) (by norm_num) aestronglyMeasurable_const
    (Filter.Eventually.of_forall fun _ => ⟨le_rfl, le_rfl⟩) (memLp_const 4)
  refine ⟨u, hu, ?_⟩
  rw [hu.eqOn_axialDisplacement (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩]
  norm_num [axialDisplacement]

-- Every weak solution of that bar vanishes at both ends.
example (u : WeakH10On 3) (_hu : IsWeakBarSolution (fun _ => 2) (fun _ => 4) u) :
    u.toFun 0 = 0 ∧ u.toFun 3 = 0 :=
  u.toFun_zero_and_length (by norm_num)

/-! ## B. Piecewise constant rigidity -/

-- The rigidity `1` on `x < 1` and `2` on `x ≥ 1`, on a bar of length `2` under the unit load,
-- satisfies the hypotheses of the existence theorem, so a weak solution exists.
example : ∃ u : WeakH10On 2, IsWeakBarSolution (stepRigidity 1 2 1) (fun _ => 1) u := by
  obtain ⟨hpos, hmeas, hbd⟩ := stepRigidity_admissible (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 2) 1 2
  obtain ⟨u, hu, -⟩ := weakBar_exists_unique (by norm_num) hpos hmeas hbd (memLp_const 1)
  exact ⟨u, hu⟩

/-! ## C. Inadmissible data -/

-- Zero rigidity under the unit load on `[0, 2]` has no weak solution.
example (u : WeakH10On 2) : ¬ IsWeakBarSolution (fun _ => 0) (fun _ => 1) u :=
  not_isWeakBarSolution_zero_rigidity (by norm_num) u

-- The negative rigidity `-1 - x` has no positive almost-everywhere lower bound on `[0, 2]`.
example : ¬ ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 2)), (1 : ℝ) ≤ -1 - x ∧ -1 - x ≤ 1 :=
  not_ae_lowerBound_of_nonpos (EA := fun x => -1 - x) (by norm_num)
    (fun _ hx => by linarith [hx.1]) (by norm_num)

-- A traction end: the fixed-free displacement with `EA = 2`, `L = 3`, `q = 4` is represented by
-- no element of `H¹₀(0, 3)`.
example :
    ¬ ∃ v : WeakH10On 3, Set.EqOn v.toFun (fixedFreeDisplacement 2 3 4) (Set.Icc 0 3) :=
  not_exists_weakH10On_eqOn_fixedFree (by norm_num) (by norm_num) (by norm_num)

end PhyslibExtTest.Elasticity.WeakAndVirtualWork

end

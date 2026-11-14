/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.Cannings

/-!
# Tests for the sampled expectations of a Cannings model

Two children sampled out of a population of three (`b = 2 < N = 3`): relabeling the two sampled
children (`expect_sampleLaw_comp_perm` with the swap) shows that both are equally likely to
descend from parent `0`; relabeling the parents (`expect_sampleLaw_perm_comp` with the swap)
shows that the first child is equally likely to descend from parent `0` or parent `1`. The
bridge `expect_sampleLaw` turns the sampled expectation of an observable of the two children
into the whole-map expectation, and the whole-map expectation is `PMF.expect` under the law
(`expect_eq_law_expect`).
-/

@[expose] public section

open MathlibExt.Biology.PopulationGenetics.Coalescent.Cannings

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.Cannings

theorem two_le_three : 2 ≤ 3 := by decide

/-- The second sampled child descends from parent `0` exactly as often as the first. -/
example (M : CanningsModel 3) :
    (M.sampleLaw two_le_three).expect (fun g => if g 1 = 0 then 1 else 0) =
      (M.sampleLaw two_le_three).expect (fun g => if g 0 = 0 then 1 else 0) := by
  have h := M.expect_sampleLaw_comp_perm (hb := two_le_three) (Equiv.swap 0 1)
    (fun g => if g 0 = 0 then (1 : ℝ) else 0)
  simpa only [Function.comp_apply, Equiv.swap_apply_left] using h

/-- The first sampled child descends from parent `1` exactly as often as from parent `0`. -/
example (M : CanningsModel 3) :
    (M.sampleLaw two_le_three).expect (fun g => if g 0 = 1 then 1 else 0) =
      (M.sampleLaw two_le_three).expect (fun g => if g 0 = 0 then 1 else 0) := by
  have h := M.expect_sampleLaw_perm_comp (hb := two_le_three) (Equiv.swap 0 1)
    (fun g => if g 0 = 0 then (1 : ℝ) else 0)
  simpa only [Function.comp_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] using h

/-- The two sampled children share a parent with the whole-map probability that children `0` and
`1` share a parent. -/
example (M : CanningsModel 3) :
    (M.sampleLaw two_le_three).expect (fun g => if g 0 = g 1 then 1 else 0) =
      M.expect (fun f => if f 0 = f 1 then 1 else 0) := by
  rw [CanningsModel.expect_sampleLaw]
  rfl

/-- The whole-map expectation is `PMF.expect` under the law of the parent map. -/
example (M : CanningsModel 3) (F : (Fin 3 → Fin 3) → ℝ) : M.expect F = M.law.expect F :=
  M.expect_eq_law_expect F

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.Cannings

#print axioms
  MathlibExt.Biology.PopulationGenetics.Coalescent.Cannings.CanningsModel.expect_sampleLaw
#print axioms
  MathlibExt.Biology.PopulationGenetics.Coalescent.Cannings.CanningsModel.expect_sampleLaw_comp_perm
#print axioms
  MathlibExt.Biology.PopulationGenetics.Coalescent.Cannings.CanningsModel.expect_sampleLaw_perm_comp
#print axioms
  MathlibExt.Biology.PopulationGenetics.Coalescent.Cannings.CanningsModel.expect_eq_law_expect

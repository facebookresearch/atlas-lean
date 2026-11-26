/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.TuranThreeValueBoundedDistribution

open MathlibExt.Analysis.TuranThreeValueBoundedDistributionWanted

-- A counterexample remains after forgetting the three distinguished values.
example : ∃ f : ℂ → ℂ, MeromorphicOn f Set.univ ∧ ¬ IsBoundedValueDistribution f := by
  by_contra! h
  apply conjecture_refuted
  intro f hf _ _
  exact h f hf

-- An identically attained finite value has infinite multiplicity.
example (w z : ℂ) : rootMultSph (fun _ => w) (some w) z = ⊤ := by
  simp [rootMultSph, rootMult, meromorphicOrderAt_const]

-- At the pole of the reciprocal, the germ contributes only to the fibre at infinity.
example : rootMultSph (fun z : ℂ => z⁻¹) none 0 = 1 ∧
    rootMultSph (fun z : ℂ => z⁻¹) (some 0) 0 = 0 := by
  have ho : meromorphicOrderAt (fun z : ℂ => z⁻¹) 0 = -1 := by
    change meromorphicOrderAt ((id : ℂ → ℂ)⁻¹) 0 = -1
    simp [meromorphicOrderAt_inv]
  have hneg : WithTop.untopD (0 : ℤ) (-1) = -1 := rfl
  simp [rootMultSph, rootMult, poleMult, ho, hneg]

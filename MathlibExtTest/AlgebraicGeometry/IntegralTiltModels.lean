/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.IntegralTiltModels

/-! The integral denominator has exactly its specified compatible sharp,
so actual all-rank valuations cannot vanish on it. This checks a genuine
geometric normalization, with no point-comparison provider assumed.
-/

open MathlibExt.RingTheory.CompleteHuberPairModels
open MathlibExt.AlgebraicGeometry.IntegralTiltModels
open ValuativeRel

variable (p : ℕ) [Fact p.Prime] (P : PerfectoidPair p)
  [D : IntegralInput p P]

example : IsUnit (sharp p P (rootElement p P)) := by
  rw [sharp_root]
  exact D.root_zero_unit

example (v : P.toHuberPair.Space) :
    ¬ v.1.relation.vle (sharp p P (rootElement p P)) 0 := by
  rw [sharp_root]
  obtain ⟨u, hu⟩ := D.root_zero_unit
  rw [← hu]
  intro h
  have h0 : v.1.relation.vle 1 0 := by
    simpa using v.1.relation.mul_vle_mul_left h (u⁻¹ : P.ringˣ)
  exact v.1.relation.not_vle_one_zero h0

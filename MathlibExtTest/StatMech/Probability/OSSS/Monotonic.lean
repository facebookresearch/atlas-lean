/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OSSS.Monotonic
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.OSSS.Monotonic`

* `condNorm` of the constant weight `1` on `Bool`-configurations over `Fin 1` with no
  conditioning is `2`.
* `fkg_implies_monotonic` for the weight `μ ω = 2` if `ω 0` is open and `1` otherwise on `Fin 1`,
  which satisfies the FKG lattice condition (proved by cases).
* `isIncreasing_openAt`.
-/

@[expose] public section

open StatMech StatMech.OSSS.Monotonic

namespace MathlibExtTest.StatMech.Probability.OSSS.Monotonic

example : condNorm (fun _ : ConfigSpace (Fin 1) => (1 : ℝ)) ∅ (fun _ => true) = 2 := by
  simp [condNorm, Agree]

/-- A weight favouring the open state. -/
noncomputable def μ (ω : ConfigSpace (Fin 1)) : ℝ := if ω 0 = true then 2 else 1

theorem μ_fkg : FKGLatticeCondition μ := by
  intro ω ω'
  cases h1 : ω 0 <;> cases h2 : ω' 0 <;> simp [μ, h1, h2]

example : IsMonotonicMeasure μ :=
  fkg_implies_monotonic (fun ω => by unfold μ; split <;> norm_num) μ_fkg

example (e : Fin 1) : IsIncreasing (OpenAt (E := Fin 1) e) := isIncreasing_openAt e

end MathlibExtTest.StatMech.Probability.OSSS.Monotonic

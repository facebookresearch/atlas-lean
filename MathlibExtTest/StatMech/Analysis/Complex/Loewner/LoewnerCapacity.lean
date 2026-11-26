/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Loewner.LoewnerCapacity

/-!
# Tests for `MathlibExt.Analysis.Complex.Loewner.LoewnerCapacity`

* `coeff_ode_solution` with `a₁ t = 2t`.
* `loewner_halfplane_capacity_eq` with the trivial model `g_t(z) = z + 2t/z` (half-disk maps),
  which satisfies both capacity hypotheses; this is non-vacuity of the hypotheses, not a Loewner
  chain.
* `tendsto_mul_loewnerField` with `G = id`, `W = 0`.
-/

@[expose] public section

open StatMech.SLE Complex Set Filter Topology

namespace MathlibExtTest.StatMech.Analysis.Complex.Loewner.LoewnerCapacity

lemma hasDerivWithinAt_two_mul (t : ℝ) : HasDerivWithinAt (fun u : ℝ => 2 * u) 2 (Ici 0) t := by
  simpa using ((hasDerivAt_id t).const_mul (2 : ℝ)).hasDerivWithinAt

example : ∀ t ∈ Ici (0 : ℝ), (fun u : ℝ => 2 * u) t = 2 * t :=
  coeff_ode_solution (fun t _ => hasDerivWithinAt_two_mul t) (by simp)

example : ∀ t ∈ Ici (0 : ℝ),
    HasHalfPlaneCapacity (fun z : ℂ => z + ((2 * t : ℝ) : ℂ) / z) (2 * t) :=
  loewner_halfplane_capacity_eq (g := fun t z => z + ((2 * t : ℝ) : ℂ) / z)
    (a₁ := fun u => 2 * u) (fun t _ => hasHalfPlaneCapacity_halfDisk (2 * t)) (by simp)
    (fun t _ => hasDerivWithinAt_two_mul t)

example : Tendsto (fun z : ℂ => z * loewnerField (fun _ => 0) 0 (id z)) (cocompact ℂ) (𝓝 2) :=
  tendsto_mul_loewnerField (fun _ => 0) 0 id (by simp)

end MathlibExtTest.StatMech.Analysis.Complex.Loewner.LoewnerCapacity

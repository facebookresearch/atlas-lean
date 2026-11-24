/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electromagnetism.SeparableGuidePotential

@[expose] public section

open PhyslibExt.Electromagnetism.SeparableGuidePotential

namespace PhyslibExtTest.Electromagnetism.SeparableGuidePotential

/-- The separable guide potential has zero scalar potential. -/
example (c : SpeedOfLight) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
    (separableGuidePotential c a f).scalarPotential c = 0 :=
  scalarPotential_separableGuidePotential c a f

/-- The vector potential is `(0, a(x) f(t, z), 0)` in physical time. -/
example (c : SpeedOfLight) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (t : Time) (p : Space) :
    (separableGuidePotential c a f).vectorPotential c t p =
      WithLp.toLp 2 ![0, a (p 0) * f t.val (p 2), 0] :=
  vectorPotential_separableGuidePotential c a f t p

/-- The electric field needs no smoothness of the spatial profile:
for zero profile and constant mode it vanishes identically. -/
example (c : SpeedOfLight) (t : Time) (p : Space) :
    (separableGuidePotential c (fun _ => 0) (fun _ _ => 0)).electricField c t p =
      WithLp.toLp 2 ![0, 0, 0] := by
  rw [electricField_separableGuidePotential c _ _ t p (hasDerivAt_const _ _)]
  simp

/-- The sinusoidal fixture's fields at the documented point. -/
example (c : SpeedOfLight) :
    (sinusoidalGuidePotential c).electricField c ⟨0⟩ ⟨![Real.pi / 2, 0, -(Real.pi / 6)]⟩ =
      WithLp.toLp 2 ![0, 2, 0] ∧
    (sinusoidalGuidePotential c).magneticField c ⟨0⟩ ⟨![Real.pi / 2, 0, -(Real.pi / 6)]⟩ =
      WithLp.toLp 2 ![-3, 0, 0] ∧
    (sinusoidalGuidePotential c).magneticField c ⟨0⟩ ⟨![0, 0, 0]⟩ 2 = 1 :=
  sinusoidal_fields_at_point c

/-- The reversed-curl-sign formula is refuted by the fixture. -/
example (c : SpeedOfLight) :
    ¬ ∀ (t : Time) (p : Space), (sinusoidalGuidePotential c).magneticField c t p 0 =
      Real.sin (p 0) * deriv (fun z => Real.cos (2 * t.val - 3 * z)) (p 2) :=
  sinusoidal_reversed_curl_sign_fails c

end PhyslibExtTest.Electromagnetism.SeparableGuidePotential

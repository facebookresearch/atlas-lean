/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Algebra.Module.Projective

/-!
# Exterior powers of projective modules

The native exterior-power map preserves the actual split embedding of a
projective module into a free one. Its exterior-power retraction proves
projectivity in every degree, without finite generation or a chosen basis.
-/

@[expose] public section

noncomputable section

universe u v

namespace exteriorPower

variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]

/-- Exterior powers preserve actual module projectivity over any commutative ring. -/
instance instProjective [Module.Projective R M] (n : ℕ) :
    Module.Projective R (⋀[R]^n M) := by
  obtain ⟨N, hNadd, hNmodule, hNfree, i, s, hsi⟩ := Module.Projective.iff_split.mp
    (inferInstance : Module.Projective R M)
  let _ : AddCommMonoid N := hNadd
  let _ : Module R N := hNmodule
  let _ : Module.Free R N := hNfree
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
  exact Module.Projective.of_split (exteriorPower.map n i) (exteriorPower.map n s)
    (by rw [← exteriorPower.map_comp, hsi, exteriorPower.map_id])

end exteriorPower

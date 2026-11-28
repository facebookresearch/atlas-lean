/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Algebra.Module.Projective

/-!
# Exterior powers of projective modules

For a commutative ring `R` and a projective `R`-module `M`, every exterior power `Λ^n_R M` is
projective. An embedding of `M` as a retract of a free module induces the corresponding
exterior-power retract.

Reference: Bourbaki, *Algebra*, Chapter III.
-/

@[expose] public section

noncomputable section

universe u v

namespace exteriorPower

variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]

/-- Let `R` be a commutative ring and `M` an `R`-module. If `M` is projective, then for every `n :
ℕ`, `Module.Projective R (Λ^n_R M)` holds. -/
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

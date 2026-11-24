/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Actual projective exterior powers have torsion-free scalar action

Projectivity earns an actual split embedding in a free module internally.
The original exterior map preserves that embedding, and the free exterior
basis has regular scalar action. Pullback therefore proves torsion-freeness
in every exterior degree, without finite rank or a supplied basis/splitting.
-/

public section
noncomputable section
namespace exteriorPower

universe u v
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Every exterior power of an actual projective module has regular scalar action. -/
theorem isTorsionFree_of_projective [Module.Projective R M] (n : ℕ) :
    Module.IsTorsionFree R (⋀[R]^n M) := by
  obtain ⟨N, hNadd, hNmodule, hNfree, i, s, hsi⟩ := Module.Projective.iff_split.mp
    (inferInstance : Module.Projective R M)
  let _ : AddCommMonoid N := hNadd
  let _ : Module R N := hNmodule
  let _ : Module.Free R N := hNfree
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
  let _ : Module.Free R (⋀[R]^n N) := inferInstance
  let _ : Module.IsTorsionFree R (⋀[R]^n N) := inferInstance
  have hi : Function.Injective (exteriorPower.map n i) := exteriorPower.map_injective s hsi
  exact hi.moduleIsTorsionFree (exteriorPower.map n i) (fun r x => map_smul _ r x)

/-- Every regular scalar of the original ring acts injectively on an actual projective exterior power. -/
theorem isSMulRegular_of_projective [Module.Projective R M] (n : ℕ) (r : R) (hr : IsRegular r) :
    IsSMulRegular (⋀[R]^n M) r := by
  let _ : Module.IsTorsionFree R (⋀[R]^n M) := isTorsionFree_of_projective n
  exact hr.isSMulRegular

end exteriorPower

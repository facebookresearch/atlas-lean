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
# Regular scalar action on projective exterior powers

For a commutative ring `R` and a projective `R`-module `M`, each exterior power is
torsion-free in the regular-scalar sense: every `r : R` whose multiplication on `R` is
injective also acts injectively on `Λ^n_R M`.

Reference: Bourbaki, *Algebra*, Chapter III.
-/

public section
noncomputable section
namespace exteriorPower

universe u v
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Let `R` be a commutative ring and `M` an `R`-module. If `M` is projective, every `Λ^n_R M`
satisfies `Module.IsTorsionFree R`. Thus for each regular `r : R`, `r • x = r • y` in `Λ^n_R
M` implies `x=y`. -/
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

/-- Let `R` be a commutative ring and `M` an `R`-module. Assume `M` is projective. For `n : ℕ` and
`r : R` with `IsRegular r`, the map `x ↦ r • x` on `Λ^n_R M` is injective, that is,
`IsSMulRegular (Λ^n_R M) r`. -/
theorem isSMulRegular_of_projective [Module.Projective R M] (n : ℕ) (r : R) (hr : IsRegular r) :
    IsSMulRegular (⋀[R]^n M) r := by
  let _ : Module.IsTorsionFree R (⋀[R]^n M) := isTorsionFree_of_projective n
  exact hr.isSMulRegular

end exteriorPower

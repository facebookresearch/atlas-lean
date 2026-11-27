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

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Tactic.Ring

/-!
# The actual state extension to forced C-star unitization

A given positive continuous functional of norm one extends by
`(z, a) ↦ z + f a`. Positivity follows from the original nonunital
C-star functional Schwarz bound. The unitization keeps its stock norm.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ComplexOrder

namespace PositiveContinuousLinearMap

universe uA

variable {A : Type uA} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]

/-- The stock spectral order on the actual forced C-star unitization. -/
local instance stateUnitizationOrder : PartialOrder (Unitization ℂ A) :=
  CStarAlgebra.spectralOrder _

/-- The matching stock ordered-star structure on the forced unitization. -/
local instance stateUnitizationStarOrder :
    @StarOrderedRing (Unitization ℂ A) _ stateUnitizationOrder _ :=
  CStarAlgebra.spectralOrderedRing _

/-- **Linear extension to the unitization.** Let `A` be a nonunital complex C*-algebra with a
star-compatible partial order and let `f : A → ℂ` be a positive continuous complex-linear
functional. On the complex unitization, the formula `(λ,a) ↦ λ + f(a)` defines a complex-linear
extension of `f` with value one at the adjoined unit. -/
def unitizationLinearExtension (f : A →P[ℂ] ℂ) : Unitization ℂ A →ₗ[ℂ] ℂ :=
  (Unitization.fstHom ℂ A).toLinearMap +
    f.toLinearMap.comp (Unitization.sndHom ℂ ℂ A)

omit [StarOrderedRing A] in
/-- **Formula for the linear unitization extension.** Let `A` be a nonunital complex C*-algebra with a
star-compatible partial order and let `f : A → ℂ` be a positive continuous complex-linear
functional. For every `(λ,a)` in the complex unitization, the linear extension has value `λ + f(a)`. -/
@[simp]
theorem unitizationLinearExtension_apply (f : A →P[ℂ] ℂ) (x : Unitization ℂ A) :
    unitizationLinearExtension f x = x.fst + f x.snd := rfl

/-- **Nonnegative variance of a nonunital state.** Let `A` be a nonunital complex C*-algebra with a
star-compatible partial order and let `f : A → ℂ` be a positive continuous complex-linear
functional. Assume that the operator norm of `f` is one. For every `a ∈ A`, `f(a* a) - |f(a)|² ≥ 0`
in the spectral order of `ℂ`. -/
theorem state_variance_nonneg (f : A →P[ℂ] ℂ)
    (hf : ‖f.toContinuousLinearMap‖ = 1) (a : A) :
    0 ≤ f (star a * a) - star (f a) * f a := by
  have hAA : 0 ≤ f (star a * a) := f.map_nonneg (star_mul_self_nonneg a)
  have hff : 0 ≤ star (f a) * f a := star_mul_self_nonneg (f a)
  have hNorm : ‖star (f a) * f a‖ ≤ ‖f (star a * a)‖ := by
    simpa only [CStarRing.norm_star_mul_self, pow_two, hf, one_mul] using
      f.norm_map_sq_le_opNorm_mul a
  apply sub_nonneg.mpr
  rw [Complex.eq_coe_norm_of_nonneg hff, Complex.eq_coe_norm_of_nonneg hAA]
  exact (RCLike.ofReal_le_ofReal (K := ℂ)).2 hNorm

/-- **Star-square formula for the unitization extension.** Let `A` be a nonunital complex C*-algebra
with a star-compatible partial order and let `f : A → ℂ` be a positive continuous complex-linear
functional. For `x = (λ,a)` in the complex unitization, the extension takes `x* x` to `|λ + f(a)|² +
f(a* a) - |f(a)|²`. -/
theorem unitizationLinearExtension_star_square (f : A →P[ℂ] ℂ)
    (x : Unitization ℂ A) :
    unitizationLinearExtension f (star x * x) =
      star (x.fst + f x.snd) * (x.fst + f x.snd) +
        (f (star x.snd * x.snd) - star (f x.snd) * f x.snd) := by
  simp only [unitizationLinearExtension_apply, Unitization.fst_mul, Unitization.snd_mul,
    Unitization.fst_star, Unitization.snd_star, map_add, map_smul, map_star,
    smul_eq_mul, star_add]
  ring

/-- **Positivity on unitization star squares.** Let `A` be a nonunital complex C*-algebra with a
star-compatible partial order and let `f : A → ℂ` be a positive continuous complex-linear
functional. Assume that the operator norm of `f` is one. For every element `x` of the complex
unitization, the extension `(λ,a) ↦ λ + f(a)` has nonnegative value at `x* x`. -/
theorem unitizationLinearExtension_square_nonneg (f : A →P[ℂ] ℂ)
    (hf : ‖f.toContinuousLinearMap‖ = 1) (x : Unitization ℂ A) :
    0 ≤ unitizationLinearExtension f (star x * x) := by
  rw [unitizationLinearExtension_star_square]
  exact add_nonneg (star_mul_self_nonneg _) (state_variance_nonneg f hf x.snd)

/-- **Positivity of the unitization extension.** Let `A` be a nonunital complex C*-algebra with a
star-compatible partial order and let `f : A → ℂ` be a positive continuous complex-linear
functional. Assume that the operator norm of `f` is one. For every positive element `x` of the
complex C*-unitization, the linear extension has nonnegative value. -/
theorem unitizationLinearExtension_nonneg (f : A →P[ℂ] ℂ)
    (hf : ‖f.toContinuousLinearMap‖ = 1) (x : Unitization ℂ A) (hx : 0 ≤ x) :
    0 ≤ unitizationLinearExtension f x := by
  have hmem := (StarOrderedRing.nonneg_iff).1 hx
  refine AddSubmonoid.closure_induction
    (motive := fun x _ => 0 ≤ unitizationLinearExtension f x) ?_ ?_ ?_ hmem
  · rintro _ ⟨y, rfl⟩
    exact unitizationLinearExtension_square_nonneg f hf y
  · simp only [map_zero, le_refl]
  · intro a b _ _ ha hb
    simpa only [map_add] using add_nonneg ha hb

/-- **Positive state on the unitization.** Let `A` be a nonunital complex C*-algebra with a
star-compatible partial order and let `f : A → ℂ` be a positive continuous complex-linear
functional. Assume that the operator norm of `f` is one. The extension `(λ,a) ↦ λ + f(a)` is a
positive complex-linear functional on the complex unitization. -/
def unitizationPositiveState (f : A →P[ℂ] ℂ) (hf : ‖f.toContinuousLinearMap‖ = 1) :
    Unitization ℂ A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (unitizationLinearExtension f) (unitizationLinearExtension_nonneg f hf)

/-- **Continuous state on the unitization.** Let `A` be a nonunital complex C*-algebra with a
star-compatible partial order and let `f : A → ℂ` be a positive continuous complex-linear
functional. Assume that the operator norm of `f` is one. The extension `(λ,a) ↦ λ + f(a)` is a
positive continuous complex-linear functional on the complex C*-unitization. -/
def unitizationState (f : A →P[ℂ] ℂ) (hf : ‖f.toContinuousLinearMap‖ = 1) :
    Unitization ℂ A →P[ℂ] ℂ :=
  PositiveContinuousLinearMap.ofClass (unitizationPositiveState f hf)

/-- **Value of the unitization state.** Let `A` be a nonunital complex C*-algebra with a star-compatible
partial order and let `f : A → ℂ` be a positive continuous complex-linear functional. Assume that
the operator norm of `f` is one. For every element `(λ,a)` of the unitization, the extended state
has value `λ + f(a)`. -/
@[simp]
theorem unitizationState_apply (f : A →P[ℂ] ℂ) (hf : ‖f.toContinuousLinearMap‖ = 1)
    (x : Unitization ℂ A) : unitizationState f hf x = x.fst + f x.snd := rfl

/-- **Restriction of the unitization state.** Let `A` be a nonunital complex C*-algebra with a
star-compatible partial order and let `f : A → ℂ` be a positive continuous complex-linear
functional. Assume that the operator norm of `f` is one. The extended state evaluates at the ideal
inclusion `(0,a)` to `f(a)` for every `a ∈ A`. -/
theorem unitizationState_inr (f : A →P[ℂ] ℂ) (hf : ‖f.toContinuousLinearMap‖ = 1) (a : A) :
    unitizationState f hf (Unitization.inr a) = f a := by
  simp only [unitizationState_apply, Unitization.fst_inr, Unitization.snd_inr, zero_add]

/-- **Value of the state at the adjoined unit.** Let `A` be a nonunital complex C*-algebra with a
star-compatible partial order and let `f : A → ℂ` be a positive continuous complex-linear
functional. Assume that the operator norm of `f` is one. The extended state takes value one at the
unit of the complex unitization. -/
theorem unitizationState_one (f : A →P[ℂ] ℂ) (hf : ‖f.toContinuousLinearMap‖ = 1) :
    unitizationState f hf (1 : Unitization ℂ A) = 1 := by
  simp only [unitizationState_apply, Unitization.fst_one, Unitization.snd_one, map_zero, add_zero]

/-- **Norm of the extended unitization state.** Let `A` be a nonunital complex C*-algebra with a
star-compatible partial order and let `f : A → ℂ` be a positive continuous complex-linear
functional. Assume that the operator norm of `f` is one. The positive continuous extension of `f` to
the complex C*-unitization has operator norm one. -/
theorem norm_unitizationState (f : A →P[ℂ] ℂ) (hf : ‖f.toContinuousLinearMap‖ = 1) :
    ‖(unitizationState f hf).toContinuousLinearMap‖ = 1 := by
  have h := (unitizationState f hf).ofReal_opNorm_eq_map_one
  rw [unitizationState_one] at h
  exact_mod_cast h

end PositiveContinuousLinearMap

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

public import MathlibExt.Analysis.CStarAlgebra.Weight.GNSCoefficientPositive
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive

/-!
# Positive continuous functionals from GNS vectors

For an extended positive weight on a unital complex C-star algebra, let `π : A → B(H_φ)` be the
GNS representation and `Λ : n_φ → H_φ` the dense domain map. Each `x ∈ n_φ` defines the bounded
complex-linear functional `ψ_x(a)=⟨Λ(x),π(a)Λ(x)⟩`.

For `a ≥ 0`, this equals `(φ(x* a x)).toReal ≥ 0`. Hence `ψ_x` is monotone for the spectral
orders and defines a positive continuous linear map `A → ℂ`. Normality of the weight or
functional is not assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MathlibExt.Analysis.CStarAlgebra

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

/-- **Positive functional of a finite square GNS vector.** Let `A` be a unital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x : φ(x* x) < ∞}`, and let `Λ : n_φ → H_φ` be its
dense GNS map. Let `π : A → B(H_φ)` be the unital star representation satisfying
`π(a)Λ(x)=Λ(a*x)`. for `x ∈ n_φ`, `gnsDiagonalPositiveFunctional φ x :
PositiveContinuousLinearMap ℂ A ℂ` has value `ψ_x(a)=⟨Λ x,π(a)Λ x⟩`; for `a ≥ 0`,
`ψ_x(a)=((φ(x* a x)).toReal : ℂ) ≥ 0`. It is bounded and monotone in the spectral orders. -/
def Weight.gnsDiagonalPositiveFunctional (φ : Weight A) (x : φ.finiteSquareSubmodule) :
    PositiveContinuousLinearMap ℂ A ℂ := by
  let ψ : StrongDual ℂ A :=
    representationCoefficient φ.gnsLeftStarAlgHom (φ.gnsMap x) (φ.gnsMap x)
  have hpositive : ∀ a : A, 0 ≤ a → 0 ≤ ψ a := by
    intro a ha
    change 0 ≤ representationCoefficient φ.gnsLeftStarAlgHom (φ.gnsMap x) (φ.gnsMap x) a
    rw [φ.gnsCoefficient_positive_value a ha x]
    let t : ℝ := (φ.value
      ⟨star (x : A) * a * (x : A), star_left_conjugate_nonneg ha (x : A)⟩).toReal
    let z : ℂ := RCLike.ofReal (Real.sqrt t)
    have ht : 0 ≤ t := ENNReal.toReal_nonneg
    have hz : star z = z := by
      change (starRingEnd ℂ) (RCLike.ofReal (Real.sqrt t) : ℂ) = _
      exact RCLike.conj_ofReal (K := ℂ) (Real.sqrt t)
    have hcast : (RCLike.ofReal (Real.sqrt t * Real.sqrt t) : ℂ) =
        (RCLike.ofReal (Real.sqrt t) : ℂ) * (RCLike.ofReal (Real.sqrt t) : ℂ) :=
      RCLike.ofReal_mul (K := ℂ) (Real.sqrt t) (Real.sqrt t)
    have hsquare : star z * z = (RCLike.ofReal t : ℂ) := by
      calc
        star z * z = z * z := by rw [hz]
        _ = (RCLike.ofReal (Real.sqrt t * Real.sqrt t) : ℂ) := hcast.symm
        _ = (RCLike.ofReal t : ℂ) :=
          congrArg (fun r : ℝ => (RCLike.ofReal r : ℂ)) (Real.mul_self_sqrt ht)
    change 0 ≤ (RCLike.ofReal t : ℂ)
    rw [← hsquare]
    exact star_mul_self_nonneg z
  exact
    { __ := ψ
      monotone' := by
        intro a b hab
        have h := hpositive (b - a) (sub_nonneg.mpr hab)
        rw [map_sub] at h
        exact sub_nonneg.mp h }

/-- **Underlying bounded diagonal GNS coefficient.** Let `A` be a unital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x : φ(x* x) < ∞}`, and let `Λ : n_φ → H_φ` be its dense GNS
map. Let `π : A → B(H_φ)` be the unital star representation satisfying `π(a)Λ(x)=Λ(a*x)`. for
`x ∈ n_φ`, forgetting positivity in `gnsDiagonalPositiveFunctional φ x` gives the continuous
complex-linear coefficient `a ↦ ⟨Λ x,π(a)Λ x⟩`. -/
theorem Weight.gnsDiagonalPositiveFunctional_toContinuousLinearMap (φ : Weight A)
    (x : φ.finiteSquareSubmodule) :
    (φ.gnsDiagonalPositiveFunctional x).toContinuousLinearMap =
      representationCoefficient φ.gnsLeftStarAlgHom (φ.gnsMap x) (φ.gnsMap x) :=
  rfl

end

end CStarAlgebra.ScalarWeight

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
# The actual diagonal GNS coefficient as a positive continuous linear map

The existing bounded diagonal coefficient retains its exact continuous
linear map. Its original positive compressed-weight value proves positivity
for the canonical spectral orders, and linearity then proves monotonicity.
The standard positive continuous linear map bundles those same values.

This supplies the positive-map field needed for an actual positive normal
functional. Normal-functional membership and the computed representation's
ultraweak continuity remain separate; no normality assumption is used here.
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

/-- The same original bounded diagonal coefficient has its actual positive continuous linear map. -/
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

/-- Forgetting positivity retains exactly the existing bounded diagonal representation coefficient. -/
theorem Weight.gnsDiagonalPositiveFunctional_toContinuousLinearMap (φ : Weight A)
    (x : φ.finiteSquareSubmodule) :
    (φ.gnsDiagonalPositiveFunctional x).toContinuousLinearMap =
      representationCoefficient φ.gnsLeftStarAlgHom (φ.gnsMap x) (φ.gnsMap x) :=
  rfl

end

end CStarAlgebra.ScalarWeight

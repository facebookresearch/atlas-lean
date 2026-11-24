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

public import MathlibExt.Analysis.CStarAlgebra.Weight.GNSLeftUnital
public import MathlibExt.Analysis.CStarAlgebra.RepresentationCoefficient
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Positive diagonal coefficients of the actual weight GNS map

The existing bounded representation coefficient at an original finite-square
vector has the original compressed positive-weight value. The actual positive
square root factors the original positive coefficient. The proved star law
and canonical dense values reduce its diagonal pairing to the original
finite-square weight value.

This is a prerequisite for ultraweak continuity of the same computed GNS
map. No normal-weight assumption or positive/normal functional certificate
is used. Positive-LUB preservation, representation normality/range, full
finite integration extension and Tomita/modular/polar data remain separate.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace
open MathlibExt.Analysis.CStarAlgebra

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

/-- The actual positive diagonal GNS coefficient is the original finite compressed weight value. -/
theorem Weight.gnsCoefficient_positive_value (φ : Weight A) (a : A) (ha : 0 ≤ a)
    (x : φ.finiteSquareSubmodule) :
    representationCoefficient φ.gnsLeftStarAlgHom (φ.gnsMap x) (φ.gnsMap x) a =
      (RCLike.ofReal ((φ.value
        ⟨star (x : A) * a * (x : A), star_left_conjugate_nonneg ha (x : A)⟩).toReal) : ℂ) := by
  let b : A := CFC.sqrt a
  have hstar : star b = b := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)
  have hsquare : b * b = a := CFC.sqrt_mul_sqrt_self a ha
  have hfactor : φ.gnsLeftStarAlgHom a =
      star (φ.gnsLeftStarAlgHom b) * φ.gnsLeftStarAlgHom b := by
    have hraw : star b * b = a := by rw [hstar]; exact hsquare
    rw [← hraw, map_mul, map_star]
  have hweightSquare : leftSquare (b * (x : A)) =
      (⟨star (x : A) * a * (x : A), star_left_conjugate_nonneg ha (x : A)⟩ : PositiveElement A) := by
    apply Subtype.ext
    change star (b * (x : A)) * (b * (x : A)) = star (x : A) * a * (x : A)
    rw [star_mul, hstar]
    calc
      star (x : A) * b * (b * (x : A)) = star (x : A) * (b * b) * (x : A) := by
        simp only [mul_assoc]
      _ = star (x : A) * a * (x : A) := by rw [hsquare]
  calc
    representationCoefficient φ.gnsLeftStarAlgHom (φ.gnsMap x) (φ.gnsMap x) a =
        ⟪φ.gnsMap x, (star (φ.gnsLeftStarAlgHom b) * φ.gnsLeftStarAlgHom b) (φ.gnsMap x)⟫_ℂ := by
      rw [representationCoefficient_apply, hfactor]
    _ = ⟪φ.gnsLeftStarAlgHom b (φ.gnsMap x), φ.gnsLeftStarAlgHom b (φ.gnsMap x)⟫_ℂ := by
      rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right]
    _ = φ.finiteSquarePolarInner (φ.finiteSquareLeftMul b x) (φ.finiteSquareLeftMul b x) := by
      simp only [φ.gnsLeftStarAlgHom_gnsMap, φ.gnsMap_inner]
    _ = (RCLike.ofReal (φ.finiteSquareValue (φ.finiteSquareLeftMul b x)) : ℂ) :=
      φ.finiteSquarePolarInner_self (φ.finiteSquareLeftMul b x)
    _ = (RCLike.ofReal ((φ.value
        ⟨star (x : A) * a * (x : A), star_left_conjugate_nonneg ha (x : A)⟩).toReal) : ℂ) := by
      change (RCLike.ofReal ((φ.value (leftSquare (b * (x : A)))).toReal) : ℂ) = _
      rw [hweightSquare]

end

end CStarAlgebra.ScalarWeight

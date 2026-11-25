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

public import MathlibExt.Analysis.CStarAlgebra.GNS.NonUnitalCyclic
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The actual nonunital state GNS space and its unitized comparison

The original coefficient image is the stock pre-GNS map followed by
completion. Its Gram form agrees with the actual unitized-state coefficient
image. Both ranges are dense, so the identity on the original algebra
extends to a genuine linear isometric equivalence of these actual spaces.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open UniformSpace Set PositiveContinuousLinearMap
open scoped ComplexOrder InnerProductSpace

namespace PositiveContinuousLinearMap

universe uA

variable {A : Type uA} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]

attribute [local instance] stateUnitizationOrder stateUnitizationStarOrder

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `f : A → ℂ`
be a positive continuous complex-linear functional of operator norm one.

The original-algebra coefficient image has dense range, not merely dense linear span, since it
is itself a linear image. -/
theorem denseRange_stateGNSMap (f : A →P[ℂ] ℂ)
    (hf : ‖f.toContinuousLinearMap‖ = 1) : DenseRange (stateGNSMap f hf) := by
  have hd := dense_stateGNSRepresentation_span f hf
  have hs :
      (Submodule.span ℂ (Set.range fun a : A =>
        stateGNSRepresentation f hf a (unitizationGNSVector f hf)) :
          Set (unitizationGNS f hf)) ⊆ Set.range (stateGNSMap f hf) := by
    change Submodule.span ℂ (Set.range fun a : A =>
      stateGNSRepresentation f hf a (unitizationGNSVector f hf)) ≤
        (stateGNSMap f hf).range
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨a, (stateGNSRepresentation_vector f hf a).symm⟩
  exact hd.mono hs

end PositiveContinuousLinearMap

namespace PositiveLinearMap

universe uA

variable {A : Type uA} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]

attribute [local instance] PositiveContinuousLinearMap.stateUnitizationOrder
  PositiveContinuousLinearMap.stateUnitizationStarOrder

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `τ : A → ℂ`
be a positive complex-linear functional.

The coefficient map into its own GNS completion. -/
def toGNS (tau : A →ₚ[ℂ] ℂ) : A →ₗ[ℂ] tau.GNS :=
  (Completion.toComplL : tau.PreGNS →L[ℂ] tau.GNS).toLinearMap.comp
    tau.toPreGNS.toLinearMap

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `τ : A → ℂ`
be a positive complex-linear functional.

The coefficient map retains the pre-GNS representative. -/
@[simp]
theorem toGNS_apply (tau : A →ₚ[ℂ] ℂ) (a : A) :
    tau.toGNS a = (tau.toPreGNS a : tau.GNS) := rfl

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `τ : A → ℂ`
be a positive complex-linear functional.

Every pre-GNS representative comes from an coefficient, so the coefficient map has dense range. -/
theorem denseRange_toGNS (tau : A →ₚ[ℂ] ℂ) : DenseRange tau.toGNS := by
  have hd : Dense (Set.range fun x : tau.PreGNS => (x : tau.GNS)) :=
    Completion.denseRange_coe
  refine hd.mono ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨tau.ofPreGNS x, ?_⟩
  simp only [toGNS_apply, tau.toPreGNS_ofPreGNS]

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `τ : A → ℂ`
be a positive complex-linear functional.

The coefficient image has the given functional's Gram form. -/
theorem toGNS_inner (tau : A →ₚ[ℂ] ℂ) (a b : A) :
    inner ℂ (tau.toGNS a) (tau.toGNS b) = tau (star a * b) := by
  rw [toGNS_apply, toGNS_apply, Completion.inner_coe, tau.preGNS_inner_def,
    tau.ofPreGNS_toPreGNS, tau.ofPreGNS_toPreGNS]

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `τ : A → ℂ`
be a positive complex-linear functional.

The representation acts on the coefficient classes. -/
theorem gnsNonUnitalStarAlgHom_toGNS (tau : A →ₚ[ℂ] ℂ) (a b : A) :
    tau.gnsNonUnitalStarAlgHom a (tau.toGNS b) = tau.toGNS (a * b) := by
  rw [toGNS_apply, tau.gnsNonUnitalStarAlgHom_apply_coe]
  simp only [tau.leftMulMapPreGNS_apply, tau.ofPreGNS_toPreGNS, toGNS_apply]

variable (tau : A →ₚ[ℂ] ℂ)
  (htau : ‖(PositiveContinuousLinearMap.ofClass tau : A →P[ℂ] ℂ).toContinuousLinearMap‖ = 1)

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `τ : A → ℂ`
be a positive complex-linear functional. Assume its associated continuous linear functional has
operator norm one.

Both coefficient images have the same state GNS norm. -/
theorem stateGNSMap_norm_toGNS (a : A) :
    ‖stateGNSMap (PositiveContinuousLinearMap.ofClass tau) htau a‖ = ‖tau.toGNS a‖ := by
  have hU : inner ℂ
      (stateGNSMap (PositiveContinuousLinearMap.ofClass tau) htau a)
      (stateGNSMap (PositiveContinuousLinearMap.ofClass tau) htau a) =
      tau (star a * a) :=
    stateGNSMap_inner (PositiveContinuousLinearMap.ofClass tau) htau a a
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
    hU, tau.toGNS_inner]

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `τ : A → ℂ`
be a positive complex-linear functional. Assume its associated continuous linear functional has
operator norm one.

The identity on the algebra extends to the unitary comparison of its GNS completion and the
unitized-state GNS space. -/
def gnsUnitizationEquiv : tau.GNS ≃ₗᵢ[ℂ]
    unitizationGNS (PositiveContinuousLinearMap.ofClass tau) htau :=
  (LinearEquiv.refl ℂ A).extendOfIsometry tau.toGNS
    (stateGNSMap (PositiveContinuousLinearMap.ofClass tau) htau)
    (denseRange_toGNS tau)
    (denseRange_stateGNSMap (PositiveContinuousLinearMap.ofClass tau) htau)
    (fun a => by
      rw [LinearEquiv.refl_apply]
      exact stateGNSMap_norm_toGNS tau htau a)

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `τ : A → ℂ`
be a positive complex-linear functional. Assume its associated continuous linear functional has
operator norm one.

The comparison sends every coefficient class to its unitized-state coefficient image. -/
theorem gnsUnitizationEquiv_toGNS (a : A) :
    gnsUnitizationEquiv tau htau (tau.toGNS a) =
      stateGNSMap (PositiveContinuousLinearMap.ofClass tau) htau a := by
  rw [gnsUnitizationEquiv, LinearEquiv.extendOfIsometry_eq]
  rfl

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `τ : A → ℂ`
be a positive complex-linear functional. Assume its associated continuous linear functional has
operator norm one.

The comparison intertwines every coefficient action. -/
theorem gnsUnitizationEquiv_intertwines (a : A) (x : tau.GNS) :
    gnsUnitizationEquiv tau htau (tau.gnsNonUnitalStarAlgHom a x) =
      stateGNSRepresentation (PositiveContinuousLinearMap.ofClass tau) htau a
        (gnsUnitizationEquiv tau htau x) := by
  refine (denseRange_toGNS tau).induction ?_
    (isClosed_eq (by fun_prop) (by fun_prop)) x
  rintro _ ⟨b, rfl⟩
  rw [tau.gnsNonUnitalStarAlgHom_toGNS, gnsUnitizationEquiv_toGNS,
    gnsUnitizationEquiv_toGNS,
    ← stateGNSRepresentation_vector (PositiveContinuousLinearMap.ofClass tau) htau b,
    ← mul_apply_eq_comp, ← map_mul]
  exact (stateGNSRepresentation_vector (PositiveContinuousLinearMap.ofClass tau) htau (a * b)).symm

end PositiveLinearMap

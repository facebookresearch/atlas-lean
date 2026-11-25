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

public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import MathlibExt.Analysis.CStarAlgebra.State.Unitization

/-!
# The literal GNS class of the forced unit

The vector is the stock GNS image of one, not a chosen cyclic model. For a
given nonunital state, its actual positive unitization provides the C-star
domain on which this construction is used.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open UniformSpace
open scoped ComplexOrder InnerProductSpace

namespace PositiveLinearMap

universe uB

variable {B : Type uB} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Let `B` be a unital complex C*-algebra with a compatible star order, and let `f : B → ℂ` be a
positive complex-linear functional.

The GNS vector represented by the coefficient unit. -/
def gnsOneVector (f : B →ₚ[ℂ] ℂ) : f.GNS :=
  (f.toPreGNS (1 : B) : f.GNS)

/-- Let `B` be a unital complex C*-algebra with a compatible star order, and let `f : B → ℂ` be a
positive complex-linear functional.

The representation sends the unit vector to the canonical GNS image of every coefficient. -/
theorem gnsOneVector_action (f : B →ₚ[ℂ] ℂ) (b : B) :
    f.gnsNonUnitalStarAlgHom b (gnsOneVector f) = (f.toPreGNS b : f.GNS) := by
  rw [gnsOneVector, f.gnsNonUnitalStarAlgHom_apply_coe, f.leftMulMapPreGNS_apply]
  simp only [f.ofPreGNS_toPreGNS, mul_one]

/-- Let `B` be a unital complex C*-algebra with a compatible star order, and let `f : B → ℂ` be a
positive complex-linear functional.

The vector's norm is computed from the positive functional. -/
theorem norm_gnsOneVector (f : B →ₚ[ℂ] ℂ) :
    ‖gnsOneVector f‖ = Real.sqrt (f 1).re := by
  rw [gnsOneVector, Completion.norm_coe, f.preGNS_norm_def,
    f.ofPreGNS_toPreGNS, star_one, one_mul]

/-- Let `B` be a unital complex C*-algebra with a compatible star order, and let `f : B → ℂ` be a
positive complex-linear functional. For the unit-norm conclusion assume `f(1)=1`.

A genuinely normalized state gives a unit-norm GNS vector. -/
theorem norm_gnsOneVector_one (f : B →ₚ[ℂ] ℂ) (hf : f 1 = 1) :
    ‖gnsOneVector f‖ = 1 := by
  simp only [norm_gnsOneVector, hf, Complex.one_re, Real.sqrt_one]

/-- Let `B` be a unital complex C*-algebra with a compatible star order, and let `f : B → ℂ` be a
positive complex-linear functional.

The positive functional is the vector coefficient of the GNS representation at the vector
represented by the algebra unit. -/
theorem gnsOneVector_state (f : B →ₚ[ℂ] ℂ) (b : B) :
    inner ℂ (gnsOneVector f) (f.gnsNonUnitalStarAlgHom b (gnsOneVector f)) = f b := by
  rw [gnsOneVector_action, gnsOneVector, Completion.inner_coe, f.preGNS_inner_def,
    f.ofPreGNS_toPreGNS, f.ofPreGNS_toPreGNS, star_one, one_mul]

/-- Let `B` be a unital complex C*-algebra with a compatible star order, and let `f : B → ℂ` be a
positive complex-linear functional.

The coefficient orbit of the unit vector has dense complex span. -/
theorem dense_gnsOneVector_span (f : B →ₚ[ℂ] ℂ) :
    Dense (Submodule.span ℂ (Set.range fun b : B =>
      f.gnsNonUnitalStarAlgHom b (gnsOneVector f)) : Set f.GNS) := by
  have hd : Dense (Set.range fun x : f.PreGNS => (x : f.GNS)) :=
    Completion.denseRange_coe
  refine hd.mono ?_
  rintro _ ⟨x, rfl⟩
  have hx : (x : f.GNS) = f.gnsNonUnitalStarAlgHom (f.ofPreGNS x) (gnsOneVector f) := by
    rw [gnsOneVector_action, f.toPreGNS_ofPreGNS]
  change (x : f.GNS) ∈ _
  rw [hx]
  exact Submodule.subset_span (Set.mem_range_self _)

end PositiveLinearMap

namespace PositiveContinuousLinearMap

universe uA

variable {A : Type uA} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]

attribute [local instance] PositiveContinuousLinearMap.stateUnitizationOrder
  PositiveContinuousLinearMap.stateUnitizationStarOrder

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `f : A → ℂ`
be a positive continuous complex-linear functional of operator norm one.

The GNS Hilbert space of the proved positive unitized state. -/
abbrev unitizationGNS (f : A →P[ℂ] ℂ) (hf : ‖f.toContinuousLinearMap‖ = 1) :=
  (unitizationState f hf).toPositiveLinearMap.GNS

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `f : A → ℂ`
be a positive continuous complex-linear functional of operator norm one.

The class of the forced unit in the unitized-state GNS space. -/
def unitizationGNSVector (f : A →P[ℂ] ℂ) (hf : ‖f.toContinuousLinearMap‖ = 1) :
    unitizationGNS f hf :=
  PositiveLinearMap.gnsOneVector (unitizationState f hf).toPositiveLinearMap

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `f : A → ℂ`
be a positive continuous complex-linear functional of operator norm one.

The given nonunital algebra maps linearly into the GNS space through its ideal embedding. -/
def stateGNSMap (f : A →P[ℂ] ℂ) (hf : ‖f.toContinuousLinearMap‖ = 1) :
    A →ₗ[ℂ] unitizationGNS f hf :=
  (Completion.toComplL : (unitizationState f hf).toPositiveLinearMap.PreGNS →L[ℂ]
    unitizationGNS f hf).toLinearMap.comp
      ((unitizationState f hf).toPositiveLinearMap.toPreGNS.toLinearMap.comp
        (Unitization.inrHom ℂ ℂ A))

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `f : A → ℂ`
be a positive continuous complex-linear functional of operator norm one.

The coefficient image is its GNS class. -/
@[simp]
theorem stateGNSMap_apply (f : A →P[ℂ] ℂ) (hf : ‖f.toContinuousLinearMap‖ = 1) (a : A) :
    stateGNSMap f hf a =
      ((unitizationState f hf).toPositiveLinearMap.toPreGNS (Unitization.inr a) :
        unitizationGNS f hf) := rfl

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `f : A → ℂ`
be a positive continuous complex-linear functional of operator norm one.

The unitalized algebra has its GNS representation. -/
def unitizationGNSRepresentation (f : A →P[ℂ] ℂ) (hf : ‖f.toContinuousLinearMap‖ = 1) :
    Unitization ℂ A →⋆ₐ[ℂ] (unitizationGNS f hf →L[ℂ] unitizationGNS f hf) :=
  (unitizationState f hf).toPositiveLinearMap.gnsStarAlgHom

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `f : A → ℂ`
be a positive continuous complex-linear functional of operator norm one.

Restriction through the ideal embedding gives the nonunital state's representation. -/
def stateGNSRepresentation (f : A →P[ℂ] ℂ) (hf : ‖f.toContinuousLinearMap‖ = 1) :
    A →⋆ₙₐ[ℂ] (unitizationGNS f hf →L[ℂ] unitizationGNS f hf) :=
  (unitizationState f hf).toPositiveLinearMap.gnsNonUnitalStarAlgHom.comp
    (Unitization.inrNonUnitalStarAlgHom ℂ A)

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `f : A → ℂ`
be a positive continuous complex-linear functional of operator norm one.

algebra elements act on the vector by their GNS images. -/
theorem stateGNSRepresentation_vector (f : A →P[ℂ] ℂ)
    (hf : ‖f.toContinuousLinearMap‖ = 1) (a : A) :
    stateGNSRepresentation f hf a (unitizationGNSVector f hf) = stateGNSMap f hf a := by
  exact PositiveLinearMap.gnsOneVector_action (unitizationState f hf).toPositiveLinearMap
    (Unitization.inr a)

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `f : A → ℂ`
be a positive continuous complex-linear functional of operator norm one.

The nonunital state has a unit-norm GNS vector without a coefficient unit in A. -/
theorem norm_unitizationGNSVector (f : A →P[ℂ] ℂ) (hf : ‖f.toContinuousLinearMap‖ = 1) :
    ‖unitizationGNSVector f hf‖ = 1 :=
  PositiveLinearMap.norm_gnsOneVector_one (unitizationState f hf).toPositiveLinearMap
    (unitizationState_one f hf)

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `f : A → ℂ`
be a positive continuous complex-linear functional of operator norm one.

The state is exactly the vector functional of its restricted representation. -/
theorem stateGNSRepresentation_state (f : A →P[ℂ] ℂ)
    (hf : ‖f.toContinuousLinearMap‖ = 1) (a : A) :
    inner ℂ (unitizationGNSVector f hf)
      (stateGNSRepresentation f hf a (unitizationGNSVector f hf)) = f a := by
  change inner ℂ (PositiveLinearMap.gnsOneVector (unitizationState f hf).toPositiveLinearMap)
    ((unitizationState f hf).toPositiveLinearMap.gnsNonUnitalStarAlgHom (Unitization.inr a)
      (PositiveLinearMap.gnsOneVector (unitizationState f hf).toPositiveLinearMap)) = _
  rw [PositiveLinearMap.gnsOneVector_state]
  exact unitizationState_inr f hf a

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `f : A → ℂ`
be a positive continuous complex-linear functional of operator norm one.

The coefficient images have the given state's scalar GNS inner product. -/
theorem stateGNSMap_inner (f : A →P[ℂ] ℂ) (hf : ‖f.toContinuousLinearMap‖ = 1) (a b : A) :
    inner ℂ (stateGNSMap f hf a) (stateGNSMap f hf b) = f (star a * b) := by
  rw [stateGNSMap_apply, stateGNSMap_apply, Completion.inner_coe,
    PositiveLinearMap.preGNS_inner_def, PositiveLinearMap.ofPreGNS_toPreGNS,
    PositiveLinearMap.ofPreGNS_toPreGNS, ← Unitization.inr_star, ← Unitization.inr_mul]
  exact unitizationState_inr f hf (star a * b)

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `f : A → ℂ`
be a positive continuous complex-linear functional of operator norm one.

The vector has dense cyclic span for the unitized C-star algebra. -/
theorem dense_unitizationGNSVector_span (f : A →P[ℂ] ℂ) (hf : ‖f.toContinuousLinearMap‖ = 1) :
    Dense (Submodule.span ℂ (Set.range fun a : Unitization ℂ A =>
      unitizationGNSRepresentation f hf a (unitizationGNSVector f hf)) :
        Set (unitizationGNS f hf)) :=
  PositiveLinearMap.dense_gnsOneVector_span (unitizationState f hf).toPositiveLinearMap

end PositiveContinuousLinearMap

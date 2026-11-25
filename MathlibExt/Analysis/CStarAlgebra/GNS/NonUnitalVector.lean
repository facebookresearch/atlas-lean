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

public import MathlibExt.Analysis.CStarAlgebra.GNS.UnitizationComparison

/-!
# The genuine cyclic unit vector on the original nonunital state GNS carrier

The actual isometric coefficient comparison transports the proved unitized
vector back to the original GNS completion. Its coefficient formula,
anchored uniqueness, unit norm, cyclicity and original algebra action are
proved without selecting data from any open theorem or changing the carrier.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open UniformSpace Set PositiveContinuousLinearMap
open scoped ComplexOrder InnerProductSpace

namespace PositiveLinearMap

universe uA

variable {A : Type uA} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]

attribute [local instance] PositiveContinuousLinearMap.stateUnitizationOrder
  PositiveContinuousLinearMap.stateUnitizationStarOrder

variable (tau : A →ₚ[ℂ] ℂ)
  (htau : ‖(PositiveContinuousLinearMap.ofClass tau : A →P[ℂ] ℂ).toContinuousLinearMap‖ = 1)

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `τ : A → ℂ`
be a positive complex-linear functional. Assume its associated continuous linear functional has
operator norm one.

The cyclic unit vector in the state-indexed GNS completion. -/
def nonunitalGNSVector : tau.GNS :=
  (gnsUnitizationEquiv tau htau).symm
    (unitizationGNSVector (PositiveContinuousLinearMap.ofClass tau) htau)

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `τ : A → ℂ`
be a positive complex-linear functional. Assume its associated continuous linear functional has
operator norm one.

The GNS comparison sends the normalized cyclic vector to the unit class in the unitized-state
GNS space. -/
theorem nonunitalGNSVector_toUnitization :
    gnsUnitizationEquiv tau htau (nonunitalGNSVector tau htau) =
      unitizationGNSVector (PositiveContinuousLinearMap.ofClass tau) htau := by
  rw [nonunitalGNSVector, LinearIsometryEquiv.apply_symm_apply]

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `τ : A → ℂ`
be a positive complex-linear functional. Assume its associated continuous linear functional has
operator norm one.

The state vector has norm one in its GNS norm. -/
theorem norm_nonunitalGNSVector : ‖nonunitalGNSVector tau htau‖ = 1 := by
  rw [nonunitalGNSVector, (gnsUnitizationEquiv tau htau).symm.norm_map,
    norm_unitizationGNSVector]

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `τ : A → ℂ`
be a positive complex-linear functional. Assume its associated continuous linear functional has
operator norm one.

Every algebra element acts by its GNS class. -/
theorem nonunitalGNSVector_action (a : A) :
    tau.gnsNonUnitalStarAlgHom a (nonunitalGNSVector tau htau) = tau.toGNS a := by
  apply (gnsUnitizationEquiv tau htau).injective
  rw [gnsUnitizationEquiv_intertwines, nonunitalGNSVector_toUnitization,
    stateGNSRepresentation_vector, gnsUnitizationEquiv_toGNS]

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `τ : A → ℂ`
be a positive complex-linear functional. Assume its associated continuous linear functional has
operator norm one.

The vector has the anchored Riesz coefficient formula against every coefficient class. -/
theorem nonunitalGNSVector_inner (a : A) :
    inner ℂ (nonunitalGNSVector tau htau) (tau.toGNS a) = tau a := by
  have h := (gnsUnitizationEquiv tau htau).inner_map_map
    (nonunitalGNSVector tau htau) (tau.toGNS a)
  rw [nonunitalGNSVector_toUnitization, gnsUnitizationEquiv_toGNS] at h
  calc
    inner ℂ (nonunitalGNSVector tau htau) (tau.toGNS a) =
        inner ℂ (unitizationGNSVector (PositiveContinuousLinearMap.ofClass tau) htau)
          (stateGNSMap (PositiveContinuousLinearMap.ofClass tau) htau a) := h.symm
    _ = tau a := by
      rw [← stateGNSRepresentation_vector (PositiveContinuousLinearMap.ofClass tau) htau a]
      exact stateGNSRepresentation_state (PositiveContinuousLinearMap.ofClass tau) htau a

/-- **Uniqueness from GNS coefficients.** Let `A` be a nonunital complex
C*-algebra with a compatible star order, and let `tau` be a positive complex
linear functional whose associated continuous functional has operator norm one.
If `y` belongs to the GNS Hilbert space of `tau` and
`tau a = inner ℂ y (tau.toGNS a)` for every `a : A`, then
`y = nonunitalGNSVector tau htau`. -/
theorem nonunitalGNSVector_unique (y : tau.GNS)
    (hy : ∀ a : A, tau a = inner ℂ y (tau.toGNS a)) :
    y = nonunitalGNSVector tau htau := by
  apply ext_inner_right ℂ
  intro z
  refine (denseRange_toGNS tau).induction ?_
    (isClosed_eq (by fun_prop) (by fun_prop)) z
  rintro _ ⟨a, rfl⟩
  exact (hy a).symm.trans (nonunitalGNSVector_inner tau htau a).symm

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order. Let `τ : A → ℂ`
be a positive complex-linear functional. Assume its associated continuous linear functional has
operator norm one.

The original-algebra orbit of the vector has dense span. -/
theorem dense_nonunitalGNSVector_span :
    Dense (Submodule.span ℂ (Set.range fun a : A =>
      tau.gnsNonUnitalStarAlgHom a (nonunitalGNSVector tau htau)) : Set tau.GNS) := by
  refine (denseRange_toGNS tau).mono ?_
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a, nonunitalGNSVector_action tau htau a⟩

end PositiveLinearMap

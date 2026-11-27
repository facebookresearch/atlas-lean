/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import Mathlib.RingTheory.GradedAlgebra.AlgHom

/-!
# Homogeneous components of graded algebra homomorphisms

This file provides the missing general API for restricting a graded
`R`-algebra homomorphism `f : 𝒜 →ₐᵍ[R] ℬ` to a single homogeneous component.

In `Mathlib.RingTheory.GradedAlgebra.RingHom` the additive restriction
`GradedRingHom.gradedAddHom` is available; the algebra version should provide
the `R`-linear analogue. This eliminates repeated ad-hoc constructions of
subtypes carrying explicit membership proofs when working with homogeneous
components in graded algebra arguments.

Main definitions:

* `GradedAlgHom.component`: the `R`-linear map `𝒜 i →ₗ[R] ℬ i`.

Main statements:

* `GradedAlgHom.coe_component`: the underlying value in the ambient
  algebra is `f`.
* `GradedAlgHom.component_id`: identity law.
* `GradedAlgHom.component_comp`: composition law.

The construction uses `f.map_mem` and the underlying `R`-algebra map. No
specialization to a particular grading monoid or base ring is made; the
typeclass assumptions follow the existing `GradedAlgHom` structure.
-/

@[expose] public section

namespace GradedAlgHom

variable {R A B C ι : Type*} [CommSemiring R]
  [Semiring A] [Semiring B] [Semiring C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  [DecidableEq ι] [AddMonoid ι]
  {𝒜 : ι → Submodule R A} {ℬ : ι → Submodule R B} {𝒞 : ι → Submodule R C}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]

/-- The `R`-linear restriction of a graded algebra homomorphism to a single
homogeneous component. For `f : 𝒜 →ₐᵍ[R] ℬ` and `i : ι`, this sends
`⟨x, hx⟩` to `⟨f x, f.map_mem hx⟩`. -/
def component (f : 𝒜 →ₐᵍ[R] ℬ) (i : ι) : 𝒜 i →ₗ[R] ℬ i where
  toFun x := ⟨f x.1, f.map_mem x.2⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' r x := Subtype.ext (by simp)

/-- The underlying value of `component` in the ambient algebra is `f`. -/
@[simp]
theorem coe_component (f : 𝒜 →ₐᵍ[R] ℬ) (i : ι) (x : 𝒜 i) :
    (f.component i x : B) = f (x : A) :=
  rfl

/-- Identity graded algebra homomorphism restricts to the identity linear map. -/
@[simp]
theorem component_id (i : ι) :
    (GradedAlgHom.id R 𝒜).component i = LinearMap.id := by
  ext x
  rfl

/-- Composition of graded algebra homomorphisms restricts to composition of
component linear maps. -/
@[simp]
theorem component_comp (g : ℬ →ₐᵍ[R] 𝒞) (f : 𝒜 →ₐᵍ[R] ℬ) (i : ι) :
    (g.comp f).component i = (g.component i).comp (f.component i) := by
  ext x
  rfl

end GradedAlgHom

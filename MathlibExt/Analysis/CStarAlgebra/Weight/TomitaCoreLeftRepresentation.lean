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

public import MathlibExt.Analysis.CStarAlgebra.Weight.TomitaCoreAlgebra
public import MathlibExt.Analysis.CStarAlgebra.Weight.GNSLeftRepresentation

/-!
# The original weighted core has its completed left regular representation

The original two-square algebra and its actual weighted GNS image are
identified by their existing source algebra maps. Compose the inverse
image map, the actual ambient core subtype and the existing completed
weight left representation. The resulting nonunital star representation
acts on the same original weighted Hilbert completion.

Every core product has the literal value Lambda(a*x). The actual complex
scalar, product and star laws follow from the existing star homomorphisms.
No normed-ring estimate, star-continuity, density, star closability or
associated-algebra/weight conclusion is supplied as an input.
Source: Connes, Noncommutative Geometry (1994), V.3 Definition 6 and the
original Aφ paragraph, preserved OCR 14358--14386.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- The original weighted core acts by its same actual completed weight left representation. -/
def Weight.tomitaCoreLeftRepresentation (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    letI := φ.tomitaCoreNonUnitalRing hφ;
    letI := φ.tomitaCoreStar hφ;
    φ.tomitaCore →⋆ₙₐ[ℂ] (φ.GNS →L[ℂ] φ.GNS) := by
  letI := φ.tomitaCoreNonUnitalRing hφ
  letI := φ.tomitaCoreStar hφ
  exact (φ.gnsLeftRepresentation.comp
    (NonUnitalStarSubalgebraClass.subtype φ.finiteStarSquareSubalgebra)).comp
      (φ.fromTomitaCoreStarAlgHom hφ)

/-- Every weighted source coefficient is the original completed operator of its actual core preimage. -/
@[simp]
theorem Weight.tomitaCoreLeftRepresentation_apply (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (ξ : φ.tomitaCore) :
    letI := φ.tomitaCoreNonUnitalRing hφ;
    letI := φ.tomitaCoreStar hφ;
    φ.tomitaCoreLeftRepresentation hφ ξ =
      φ.gnsLeftRepresentation ((φ.tomitaCoreEquiv hφ).symm ξ : A) := by
  let := φ.tomitaCoreNonUnitalRing hφ
  let := φ.tomitaCoreStar hφ
  rfl

/-- The same representation keeps every original two-square-finite algebra coefficient. -/
theorem Weight.tomitaCoreLeftRepresentation_original (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (a : φ.finiteStarSquareSubalgebra) :
    letI := φ.tomitaCoreNonUnitalRing hφ;
    letI := φ.tomitaCoreStar hφ;
    φ.tomitaCoreLeftRepresentation hφ (φ.tomitaCoreEquiv hφ a) = φ.gnsLeftRepresentation (a : A) := by
  let := φ.tomitaCoreNonUnitalRing hφ
  let := φ.tomitaCoreStar hφ
  rw [φ.tomitaCoreLeftRepresentation_apply, LinearEquiv.symm_apply_apply]

/-- The actual completed operator acts on every original finite-square vector by original multiplication. -/
theorem Weight.tomitaCoreLeftRepresentation_gnsMap (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (ξ : φ.tomitaCore) (x : φ.finiteSquareSubmodule) :
    letI := φ.tomitaCoreNonUnitalRing hφ;
    letI := φ.tomitaCoreStar hφ;
    φ.tomitaCoreLeftRepresentation hφ ξ (φ.gnsMap x) =
      φ.gnsMap (φ.finiteSquareLeftMul ((φ.tomitaCoreEquiv hφ).symm ξ : A) x) := by
  let := φ.tomitaCoreNonUnitalRing hφ
  let := φ.tomitaCoreStar hφ
  rw [φ.tomitaCoreLeftRepresentation_apply]
  exact φ.gnsLeftRepresentation_gnsMap _ x

/-- The original completed left action preserves the literal weighted core and its original product. -/
theorem Weight.tomitaCoreLeftRepresentation_coreAction (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (ξ η : φ.tomitaCore) :
    letI := φ.tomitaCoreNonUnitalRing hφ;
    letI := φ.tomitaCoreStar hφ;
    φ.tomitaCoreLeftRepresentation hφ ξ (η : φ.GNS) = (φ.tomitaCoreProduct hφ ξ η : φ.GNS) := by
  let := φ.tomitaCoreNonUnitalRing hφ
  let := φ.tomitaCoreStar hφ
  obtain ⟨a, rfl⟩ := (φ.tomitaCoreEquiv hφ).surjective ξ
  obtain ⟨x, rfl⟩ := (φ.tomitaCoreEquiv hφ).surjective η
  rw [φ.tomitaCoreLeftRepresentation_original, φ.tomitaCoreProduct_original,
    φ.tomitaCoreEquiv_apply, φ.tomitaCoreEquiv_apply,
    φ.finiteStarSquareGNSMap_apply, φ.finiteStarSquareGNSMap_apply]
  rw [φ.gnsLeftRepresentation_gnsMap]
  rfl

end

end CStarAlgebra.ScalarWeight

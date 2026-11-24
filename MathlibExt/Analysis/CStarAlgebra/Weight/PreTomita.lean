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

public import MathlibExt.Analysis.CStarAlgebra.Weight.GNSCompletion
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Star.Module

/-!
# The original weight core and its pre-Tomita operator

The original two-square-finite star algebra maps to the actual weight GNS
completion by the same canonical finite-square map. Original positive-zero
faithfulness makes this map injective. Its literal image is the complex
operator domain. Transporting the original algebra star through the stock
injective range equivalence gives the exact semilinear involution
`Lambda(x) -> Lambda(star x)` on that image.

The domain carries the norm inherited from the weight completion. The
ambient algebra norm is not used to claim continuity of the weight map
or its star operation. Density, closability, a closed Tomita operator,
polar decomposition and modular actions are separate source obligations.
No representation, integration extension or operator is selected from an
open source theorem. The stock inverse of an injective map identifies
unique original core elements in its literal range.

Source: Connes, Noncommutative Geometry (1994), V.3 Definition 6 and the
original NSF-weight algebra paragraph; preserved OCR 14358--14386,
SHA256 e968b4b9604a8b9a789a202dbb0f241793c10958a8a6962bc367e67a4820b9b3.
The source first-variable inner product phi(y*x) is transported by argument
reversal to the fixed Lean convention phi(x*y); the star operation stays
unchanged. This raw domain/operator supplies the actual object needed to
state the source closability and modular polar conclusions.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- The original two-square-finite core maps by the same canonical finite-square GNS map. -/
def Weight.finiteStarSquareGNSMap (φ : Weight A) : φ.finiteStarSquareSubalgebra →ₗ[ℂ] φ.GNS :=
  φ.gnsMap.comp (LinearMap.codRestrict φ.finiteSquareSubmodule
    φ.finiteStarSquareSubalgebra.toSubmodule.subtype fun x => x.property.1)

/-- The core map preserves the original element and its actual canonical GNS value. -/
@[simp]
theorem Weight.finiteStarSquareGNSMap_apply (φ : Weight A) (x : φ.finiteStarSquareSubalgebra) :
    φ.finiteStarSquareGNSMap x = φ.gnsMap ⟨(x : A), x.property.1⟩ :=
  rfl

/-- Original positive-zero faithfulness makes the actual two-square core map injective. -/
theorem Weight.finiteStarSquareGNSMap_injective (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    Function.Injective φ.finiteStarSquareGNSMap := by
  intro x y hxy
  apply Subtype.ext
  have h := φ.gnsMap_injective hφ hxy
  exact congrArg (fun z : φ.finiteSquareSubmodule => (z : A)) h

/-- The pre-Tomita domain is exactly the original two-square core image in the weight completion. -/
def Weight.tomitaCore (φ : Weight A) : Submodule ℂ φ.GNS :=
  LinearMap.range φ.finiteStarSquareGNSMap

/-- Actual domain membership is precisely an original finite-star-square GNS image. -/
theorem Weight.mem_tomitaCore (φ : Weight A) (ξ : φ.GNS) :
    ξ ∈ φ.tomitaCore ↔ ∃ x : φ.finiteStarSquareSubalgebra, φ.finiteStarSquareGNSMap x = ξ :=
  Iff.rfl

/-- The stock injective range equivalence identifies the unique original element of the actual core. -/
def Weight.tomitaCoreEquiv (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    φ.finiteStarSquareSubalgebra ≃ₗ[ℂ] φ.tomitaCore :=
  LinearEquiv.ofInjective φ.finiteStarSquareGNSMap (φ.finiteStarSquareGNSMap_injective hφ)

/-- The literal core identification has the same original canonical coefficient value. -/
@[simp]
theorem Weight.tomitaCoreEquiv_apply (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (x : φ.finiteStarSquareSubalgebra) :
    (φ.tomitaCoreEquiv hφ x : φ.GNS) = φ.finiteStarSquareGNSMap x :=
  rfl

/-- Original star transports to the same conjugate-linear involution on the literal GNS core. -/
def Weight.preTomitaCore (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    φ.tomitaCore ≃ₗ⋆[ℂ] φ.tomitaCore :=
  ((φ.tomitaCoreEquiv hφ).symm.trans (starLinearEquiv ℂ)).trans (φ.tomitaCoreEquiv hφ)

/-- The actual core involution sends the original Lambda(x) exactly to Lambda(star x). -/
theorem Weight.preTomitaCore_apply (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (x : φ.finiteStarSquareSubalgebra) :
    φ.preTomitaCore hφ (φ.tomitaCoreEquiv hφ x) = φ.tomitaCoreEquiv hφ (star x) := by
  change φ.tomitaCoreEquiv hφ (star ((φ.tomitaCoreEquiv hφ).symm (φ.tomitaCoreEquiv hφ x))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Applying the original core star twice returns every actual domain vector. -/
theorem Weight.preTomitaCore_involutive (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    Function.Involutive (φ.preTomitaCore hφ) := by
  intro ξ
  change φ.tomitaCoreEquiv hφ
    (star ((φ.tomitaCoreEquiv hφ).symm
      (φ.tomitaCoreEquiv hφ (star ((φ.tomitaCoreEquiv hφ).symm ξ))))) = ξ
  rw [LinearEquiv.symm_apply_apply, star_star, LinearEquiv.apply_symm_apply]

/-- The original pre-Tomita operator maps its literal domain into the same weight GNS completion. -/
def Weight.preTomitaOperator (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    φ.tomitaCore →ₗ⋆[ℂ] φ.GNS :=
  φ.tomitaCore.subtype.comp (φ.preTomitaCore hφ).toLinearMap

/-- The raw operator has precisely the original star value on every actual two-square core element. -/
theorem Weight.preTomitaOperator_apply (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (x : φ.finiteStarSquareSubalgebra) :
    φ.preTomitaOperator hφ (φ.tomitaCoreEquiv hφ x) = φ.finiteStarSquareGNSMap (star x) := by
  change (φ.preTomitaCore hφ (φ.tomitaCoreEquiv hφ x) : φ.GNS) = _
  rw [φ.preTomitaCore_apply]
  rfl

/-- The original involution and literal range inclusion make the raw operator injective. -/
theorem Weight.preTomitaOperator_injective (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    Function.Injective (φ.preTomitaOperator hφ) :=
  Subtype.coe_injective.comp (φ.preTomitaCore hφ).injective

end

end CStarAlgebra.ScalarWeight

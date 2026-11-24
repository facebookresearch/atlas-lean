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

public import MathlibExt.Analysis.CStarAlgebra.Weight.PreTomita
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# The original pre-Tomita operator as stock partial maps

The original two-square GNS image is the domain of the same semilinear
pre-Tomita operator. This file bundles it as the existing complex
`LinearPMap` and as a real-linear `LinearPMap` on the same actual carrier.
Complex conjugation fixes real scalars, so the real view keeps every
original operator value. The norm and topology are those of the same
weight Hilbert completion.

The real view lets Connes V.3 Definition 6 state closability using stock
`LinearPMap.IsClosable`. No parallel closability predicate, selected closed
operator, density, closability proof or modular/polar data is introduced.
Source: Connes, Noncommutative Geometry (1994), V.3 Definition 6 and the
original NSF-weight core paragraph, preserved OCR 14358--14386.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- The stock complex partial map has the original weight core and semilinear pre-Tomita values. -/
def Weight.preTomitaPMap (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    φ.GNS →ₛₗ.[starRingEnd ℂ] φ.GNS where
  domain := φ.tomitaCore
  toFun := φ.preTomitaOperator hφ

/-- The complex partial map retains exactly the original two-square GNS image domain. -/
@[simp]
theorem Weight.preTomitaPMap_domain (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    (φ.preTomitaPMap hφ).domain = φ.tomitaCore :=
  rfl

/-- The stock complex partial map has every original starred GNS coefficient value. -/
theorem Weight.preTomitaPMap_apply (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (x : φ.finiteStarSquareSubalgebra) :
    φ.preTomitaPMap hφ (φ.tomitaCoreEquiv hφ x) = φ.finiteStarSquareGNSMap (star x) :=
  φ.preTomitaOperator_apply hφ x

/-- The original raw operator as a stock real partial map on the same weighted Hilbert carrier. -/
def Weight.preTomitaRealPMap (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    φ.GNS →ₗ.[ℝ] φ.GNS where
  domain := φ.tomitaCore.restrictScalars ℝ
  toFun := {
    toFun ξ := φ.preTomitaOperator hφ ⟨ξ.val, ξ.property⟩
    map_add' := by
      intro ξ η
      change φ.preTomitaOperator hφ
        ((⟨ξ.val, ξ.property⟩ : φ.tomitaCore) + ⟨η.val, η.property⟩) = _
      exact (φ.preTomitaOperator hφ).map_add _ _
    map_smul' := by
      intro c ξ
      let ζ : φ.tomitaCore := ⟨ξ.val, ξ.property⟩
      change φ.preTomitaOperator hφ (c • ζ) = c • φ.preTomitaOperator hφ ζ
      rw [← algebraMap_smul ℂ c ζ]
      have hs : φ.preTomitaOperator hφ (algebraMap ℝ ℂ c • ζ) =
          star (algebraMap ℝ ℂ c) • φ.preTomitaOperator hφ ζ :=
        (φ.preTomitaOperator hφ).map_smul' (algebraMap ℝ ℂ c) ζ
      have hc : star (algebraMap ℝ ℂ c) = algebraMap ℝ ℂ c := by simp
      calc
        φ.preTomitaOperator hφ (algebraMap ℝ ℂ c • ζ) =
            star (algebraMap ℝ ℂ c) • φ.preTomitaOperator hφ ζ := hs
        _ = c • φ.preTomitaOperator hφ ζ := by
          rw [hc]
          exact algebraMap_smul ℂ c (φ.preTomitaOperator hφ ζ)
  }

/-- The real view changes only the scalar field of the same original complex domain. -/
@[simp]
theorem Weight.preTomitaRealPMap_domain (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    (φ.preTomitaRealPMap hφ).domain = φ.tomitaCore.restrictScalars ℝ :=
  rfl

/-- Every actual real-domain vector keeps exactly the original pre-Tomita operator value. -/
theorem Weight.preTomitaRealPMap_apply (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (ξ : φ.tomitaCore.restrictScalars ℝ) :
    φ.preTomitaRealPMap hφ ξ = φ.preTomitaOperator hφ ⟨ξ.val, ξ.property⟩ :=
  rfl

/-- The real partial map keeps the same original Lambda(x) to Lambda(star x) formula. -/
theorem Weight.preTomitaRealPMap_originalValue (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (x : φ.finiteStarSquareSubalgebra) :
    φ.preTomitaRealPMap hφ (φ.tomitaCoreEquiv hφ x) = φ.finiteStarSquareGNSMap (star x) :=
  φ.preTomitaOperator_apply hφ x

end

end CStarAlgebra.ScalarWeight

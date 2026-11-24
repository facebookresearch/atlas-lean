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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalFunctional
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive

/-!
# Actual positive normal functionals through positive continuous linear maps

The index stores Mathlib's positive continuous linear map on the original
concrete algebra, together with membership of that same bounded functional
in the actual normal-functional space. The source and scalar orders are
the canonical spectral orders. A lossless equivalence retains the complete
original family of normal functionals with monotonicity.

Evaluation and norm use the original continuous linear map. Positivity,
linearity and continuity come from the existing positive-map bundle.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An actual positive continuous linear map whose original bounded functional is normal. -/
def PositiveNormalFunctional (M : VonNeumannAlgebra H) : Type u :=
  letI : PartialOrder M := CStarAlgebra.spectralOrder M
  letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  {φ : M →P[ℂ] ℂ // φ.toContinuousLinearMap ∈ normalFunctionalSpace M}

namespace PositiveNormalFunctional

variable {M : VonNeumannAlgebra H}

/-- The same original functional as Mathlib's actual positive continuous linear map. -/
def toPositiveContinuousLinearMap (φ : PositiveNormalFunctional M) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    M →P[ℂ] ℂ := by
  letI : PartialOrder M := CStarAlgebra.spectralOrder M
  letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  exact φ.1

/-- The original continuous linear functional underlying the positive normal map. -/
def toContinuousLinearMap (φ : PositiveNormalFunctional M) : StrongDual ℂ M := by
  letI : PartialOrder M := CStarAlgebra.spectralOrder M
  letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  exact φ.1.toContinuousLinearMap

/-- The normal-functional subtype contains that literal original bounded functional. -/
def toNormalFunctionalSpace (φ : PositiveNormalFunctional M) : normalFunctionalSpace M :=
  ⟨φ.toContinuousLinearMap, φ.2⟩

instance : Coe (PositiveNormalFunctional M) (StrongDual ℂ M) :=
  ⟨toContinuousLinearMap⟩

instance : CoeFun (PositiveNormalFunctional M) (fun _ => M → ℂ) :=
  ⟨fun φ => φ.1⟩

/-- The bounded-functional and function views have exactly the same values. -/
@[simp]
theorem toContinuousLinearMap_apply (φ : PositiveNormalFunctional M) (x : M) :
    φ.toContinuousLinearMap x = φ x :=
  rfl

/-- Normal-space evaluation retains the same original functional values. -/
@[simp]
theorem toNormalFunctionalSpace_apply (φ : PositiveNormalFunctional M) (x : M) :
    (φ.toNormalFunctionalSpace : StrongDual ℂ M) x = φ x :=
  rfl

/-- The positive-map projection retains the original continuous linear map. -/
theorem toPositiveContinuousLinearMap_toContinuousLinearMap (φ : PositiveNormalFunctional M) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    φ.toPositiveContinuousLinearMap.toContinuousLinearMap = φ.toContinuousLinearMap := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  rfl

/-- The normal-space norm is the original continuous-dual operator norm. -/
theorem norm_toNormalFunctionalSpace (φ : PositiveNormalFunctional M) :
    ‖φ.toNormalFunctionalSpace‖ = ‖φ.toContinuousLinearMap‖ :=
  rfl

/-- The original functional is monotone for exactly the two canonical spectral orders. -/
theorem monotone (φ : PositiveNormalFunctional M) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    Monotone (φ : StrongDual ℂ M) := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  exact φ.1.monotone'

/-- Actual positive normal functionals preserve every canonically nonnegative element. -/
theorem apply_nonneg (φ : PositiveNormalFunctional M) (x : M) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    0 ≤ x → 0 ≤ φ x := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro hx
  exact φ.1.map_nonneg hx

/-- A Mathlib positive continuous linear map with actual normal membership gives the same index. -/
def ofPositiveContinuousLinearMap (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    (φ : M →P[ℂ] ℂ) → φ.toContinuousLinearMap ∈ normalFunctionalSpace M →
      PositiveNormalFunctional M := by
  letI : PartialOrder M := CStarAlgebra.spectralOrder M
  letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro φ hφ
  exact ⟨φ, hφ⟩

/-- Package any member of the complete original normal-and-monotone family through Mathlib's bundle. -/
def ofNormalFunctional (M : VonNeumannAlgebra H) (φ : normalFunctionalSpace M)
    (hφ : letI : PartialOrder M := CStarAlgebra.spectralOrder M
      letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
      Monotone (φ : StrongDual ℂ M)) : PositiveNormalFunctional M := by
  letI : PartialOrder M := CStarAlgebra.spectralOrder M
  letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  refine ⟨{ __ := (φ : StrongDual ℂ M), monotone' := hφ }, ?_⟩
  change (φ : StrongDual ℂ M) ∈ normalFunctionalSpace M
  exact φ.property

/-- Construction from an original normal functional preserves its literal bounded map. -/
theorem toContinuousLinearMap_ofNormalFunctional (M : VonNeumannAlgebra H)
    (φ : normalFunctionalSpace M)
    (hφ : letI : PartialOrder M := CStarAlgebra.spectralOrder M
      letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
      Monotone (φ : StrongDual ℂ M)) :
    (ofNormalFunctional M φ hφ : StrongDual ℂ M) = (φ : StrongDual ℂ M) :=
  rfl

/-- Construction recovers the same original normal-space element. -/
theorem toNormalFunctionalSpace_ofNormalFunctional (M : VonNeumannAlgebra H)
    (φ : normalFunctionalSpace M)
    (hφ : letI : PartialOrder M := CStarAlgebra.spectralOrder M
      letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
      Monotone (φ : StrongDual ℂ M)) :
    (ofNormalFunctional M φ hφ).toNormalFunctionalSpace = φ := by
  apply Subtype.ext
  rfl

/-- The entire old normal-and-monotone family and the actual positive-map index are equivalent. -/
def equivNormalMonotone (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    PositiveNormalFunctional M ≃
      {φ : normalFunctionalSpace M // Monotone (φ : StrongDual ℂ M)} := by
  letI : PartialOrder M := CStarAlgebra.spectralOrder M
  letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  refine
    { toFun := fun φ => ⟨φ.toNormalFunctionalSpace, φ.1.monotone'⟩
      invFun := fun φ => ofNormalFunctional M φ.1 φ.2
      left_inv := ?_
      right_inv := ?_ }
  · intro φ
    apply Subtype.ext
    apply PositiveContinuousLinearMap.ext
    intro x
    rfl
  · intro φ
    apply Subtype.ext
    apply Subtype.ext
    rfl

end PositiveNormalFunctional

end

end VonNeumannAlgebra

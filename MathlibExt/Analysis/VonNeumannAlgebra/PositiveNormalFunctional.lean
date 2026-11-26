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
# Positive bounded normal functionals

For a concrete von Neumann algebra `M`, a positive normal functional is a positive bounded
complex-linear map `φ : M → ℂ` whose continuous functional belongs to `M_*`, the norm-closed
span of vector functionals. Positivity and monotonicity use the canonical spectral orders.

The positive-map, bounded-functional and normal-space views have the same values and inherited
dual norm. Positive normal functionals are equivalent to monotone members of `M_*`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Positive continuous functional with normal membership.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. `PositiveNormalFunctional M` is the subtype of positive continuous complex-linear
maps `φ : M → ℂ` with underlying functional in `M_*`. -/
def PositiveNormalFunctional (M : VonNeumannAlgebra H) : Type u :=
  letI : PartialOrder M := CStarAlgebra.spectralOrder M
  letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  {φ : M →P[ℂ] ℂ // φ.toContinuousLinearMap ∈ normalFunctionalSpace M}

namespace PositiveNormalFunctional

variable {M : VonNeumannAlgebra H}

/-- **Positive continuous map of a normal functional.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its
vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Let `φ` be a positive bounded complex-linear functional belonging to `M_*`.
`φ.toPositiveContinuousLinearMap` is the positive bounded map `M → ℂ` with value `φ(x)`. -/
def toPositiveContinuousLinearMap (φ : PositiveNormalFunctional M) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    M →P[ℂ] ℂ := by
  letI : PartialOrder M := CStarAlgebra.spectralOrder M
  letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  exact φ.1

/-- **Underlying bounded positive normal functional.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its
vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Let `φ` be a positive bounded complex-linear functional belonging to `M_*`.
`φ.toContinuousLinearMap ∈ M*` is the bounded complex-linear map `x ↦ φ(x)`. -/
def toContinuousLinearMap (φ : PositiveNormalFunctional M) : StrongDual ℂ M := by
  letI : PartialOrder M := CStarAlgebra.spectralOrder M
  letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  exact φ.1.toContinuousLinearMap

/-- **Positive normal functional as a predual element.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its
vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Let `φ` be a positive bounded complex-linear functional belonging to `M_*`.
`φ.toNormalFunctionalSpace ∈ M_*` has underlying continuous functional `φ`. -/
def toNormalFunctionalSpace (φ : PositiveNormalFunctional M) : normalFunctionalSpace M :=
  ⟨φ.toContinuousLinearMap, φ.2⟩

instance : Coe (PositiveNormalFunctional M) (StrongDual ℂ M) :=
  ⟨toContinuousLinearMap⟩

instance : CoeFun (PositiveNormalFunctional M) (fun _ => M → ℂ) :=
  ⟨fun φ => φ.1⟩

/-- **Value of the bounded positive normal map.** Let `H` be a complete complex Hilbert space
and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector
functionals. Let `M_*` be their norm-closed complex span in the continuous dual `M*`. Let
`φ` be a positive bounded complex-linear functional belonging to `M_*`. for `x∈M`,
`φ.toContinuousLinearMap x=φ(x)`. -/
@[simp]
theorem toContinuousLinearMap_apply (φ : PositiveNormalFunctional M) (x : M) :
    φ.toContinuousLinearMap x = φ x :=
  rfl

/-- **Predual evaluation of a positive normal functional.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Let `φ` be a positive bounded complex-linear functional belonging to `M_*`. for
`x∈M`, `(φ.toNormalFunctionalSpace)(x)=φ(x)`. -/
@[simp]
theorem toNormalFunctionalSpace_apply (φ : PositiveNormalFunctional M) (x : M) :
    (φ.toNormalFunctionalSpace : StrongDual ℂ M) x = φ x :=
  rfl

/-- **Agreement of positive and bounded map views.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its
vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Let `φ` be a positive bounded complex-linear functional belonging to `M_*`. the
continuous-linear map underlying `φ.toPositiveContinuousLinearMap` equals
`φ.toContinuousLinearMap`. -/
theorem toPositiveContinuousLinearMap_toContinuousLinearMap (φ : PositiveNormalFunctional M) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    φ.toPositiveContinuousLinearMap.toContinuousLinearMap = φ.toContinuousLinearMap := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  rfl

/-- **Inherited dual norm of a positive normal predual element.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. Let `φ` be a positive bounded complex-linear functional
belonging to `M_*`. `‖φ.toNormalFunctionalSpace‖=‖φ.toContinuousLinearMap‖`. -/
theorem norm_toNormalFunctionalSpace (φ : PositiveNormalFunctional M) :
    ‖φ.toNormalFunctionalSpace‖ = ‖φ.toContinuousLinearMap‖ :=
  rfl

/-- **Spectral-order monotonicity of a positive normal functional.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. Let `φ` be a positive bounded complex-linear functional
belonging to `M_*`. `a≤b` in `M` implies `φ(a)≤φ(b)` in the spectral order of `ℂ`. -/
theorem monotone (φ : PositiveNormalFunctional M) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    Monotone (φ : StrongDual ℂ M) := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  exact φ.1.monotone'

/-- **Positive element has a nonnegative normal-functional value.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. Let `φ` be a positive bounded complex-linear functional
belonging to `M_*`. if `x∈M` is positive, then `φ(x)≥0` in the spectral order of `ℂ`. -/
theorem apply_nonneg (φ : PositiveNormalFunctional M) (x : M) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    0 ≤ x → 0 ≤ φ x := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro hx
  exact φ.1.map_nonneg hx

/-- **Positive normal functional from a positive bounded map.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. if a positive continuous complex-linear map `φ : M → ℂ` belongs to `M_*`,
`ofPositiveContinuousLinearMap M φ` bundles that map as a positive normal functional. -/
def ofPositiveContinuousLinearMap (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    (φ : M →P[ℂ] ℂ) → φ.toContinuousLinearMap ∈ normalFunctionalSpace M →
      PositiveNormalFunctional M := by
  letI : PartialOrder M := CStarAlgebra.spectralOrder M
  letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro φ hφ
  exact ⟨φ, hφ⟩

/-- **Positive normal map from a monotone predual member.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. if `φ∈M_*` is monotone for the spectral orders of `M` and `ℂ`, `ofNormalFunctional M
φ` is the positive normal functional with the same bounded map. -/
def ofNormalFunctional (M : VonNeumannAlgebra H) (φ : normalFunctionalSpace M)
    (hφ : letI : PartialOrder M := CStarAlgebra.spectralOrder M
      letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
      Monotone (φ : StrongDual ℂ M)) : PositiveNormalFunctional M := by
  letI : PartialOrder M := CStarAlgebra.spectralOrder M
  letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  refine ⟨{ __ := (φ : StrongDual ℂ M), monotone' := hφ }, ?_⟩
  change (φ : StrongDual ℂ M) ∈ normalFunctionalSpace M
  exact φ.property

/-- **Bounded value of a monotone-predual construction.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. for monotone `φ∈M_*`, the continuous functional underlying `ofNormalFunctional M φ`
equals `φ`. -/
theorem toContinuousLinearMap_ofNormalFunctional (M : VonNeumannAlgebra H)
    (φ : normalFunctionalSpace M)
    (hφ : letI : PartialOrder M := CStarAlgebra.spectralOrder M
      letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
      Monotone (φ : StrongDual ℂ M)) :
    (ofNormalFunctional M φ hφ : StrongDual ℂ M) = (φ : StrongDual ℂ M) :=
  rfl

/-- **Recovery of the monotone normal-space element.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its
vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. for monotone `φ∈M_*`, `(ofNormalFunctional M φ).toNormalFunctionalSpace=φ`. -/
theorem toNormalFunctionalSpace_ofNormalFunctional (M : VonNeumannAlgebra H)
    (φ : normalFunctionalSpace M)
    (hφ : letI : PartialOrder M := CStarAlgebra.spectralOrder M
      letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
      Monotone (φ : StrongDual ℂ M)) :
    (ofNormalFunctional M φ hφ).toNormalFunctionalSpace = φ := by
  apply Subtype.ext
  rfl

/-- **Positive normal functionals are monotone predual members.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. `equivNormalMonotone M` is the equivalence between
`PositiveNormalFunctional M` and `{φ∈M_* : φ is monotone}`, retaining each functional's
values. -/
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

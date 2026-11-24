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

public import MathlibExt.Analysis.CStarAlgebra.ContinuousMap.ZeroAtInftyFlip
public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Homotopy
public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.ZeroAtInfty

/-!
# Suspension representatives of uniform asymptotic morphisms

A given uniform asymptotic morphism acts on the canonical suspension by the
already constructed full-norm `C₀` lift. Since a raw family need not preserve
zero at finite time, the honest formula uses its literal zero normalization:

`f ↦ fun x ↦ φ_t (f x) - φ_t 0`.

A whole uniform homotopy suspends coherently. The construction first applies
the same `C₀` lift to its interval-valued family and then uses the existing
compact-interval/function-at-infinity flip. Thus the output is one genuine
homotopy, not separately selected time or interval slices.

This is reusable representative data motivated by Blackadar 25.2.2. It does
not select a uniform replacement, descend to all homotopy classes, construct
maximal tensor products or assert that the resulting class map is defined.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra ZeroAtInfty

namespace AsymptoticMorphism

universe uA uB

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The normalized suspension representative attached to a given uniform
asymptotic morphism. No uniform representative is selected here. -/
noncomputable def normalizedUniformSuspension
    (φ : AsymptoticMorphism A B) (hφ : IsUniform φ) :
    AsymptoticMorphism C₀(ℝ, A) C₀(ℝ, B) :=
  uniformC0Morphism (X := ℝ) φ hφ

/-- Exact coefficient formula for the normalized suspension representative. -/
@[simp]
theorem normalizedUniformSuspension_apply
    (φ : AsymptoticMorphism A B) (hφ : IsUniform φ)
    (t : AsymptoticTime) (f : C₀(ℝ, A)) (x : ℝ) :
    normalizedUniformSuspension φ hφ t f x = φ t (f x) - φ t 0 := by
  change uniformC0Morphism (X := ℝ) φ hφ t f x = _
  rw [uniformC0Morphism_apply, normalize_apply]

/-- Suspension preserves the supplied representative's genuine uniformity. -/
theorem isUniform_normalizedUniformSuspension
    (φ : AsymptoticMorphism A B) (hφ : IsUniform φ) :
    IsUniform (normalizedUniformSuspension φ hφ) := by
  simpa only [normalizedUniformSuspension] using
    (isUniform_uniformC0Morphism (X := ℝ) φ hφ)

/-- For an exactly zero-preserving input, the normalized construction is the
literal pointwise suspension formula. -/
theorem normalizedUniformSuspension_apply_of_zero
    (φ : AsymptoticMorphism A B) (hφ : IsUniform φ)
    (hzero : ∀ t : AsymptoticTime, φ t 0 = 0)
    (t : AsymptoticTime) (f : C₀(ℝ, A)) (x : ℝ) :
    normalizedUniformSuspension φ hφ t f x = φ t (f x) := by
  rw [normalizedUniformSuspension_apply, hzero, sub_zero]

/-- Suspend one whole uniform interval-valued family and flip its interval and
vanishing-at-infinity variables. -/
noncomputable def normalizedUniformSuspensionHomotopyFamily
    {φ ψ : AsymptoticMorphism A B} (H : Homotopy φ ψ)
    (hH : IsUniform H.family) :
    AsymptoticMorphism C₀(ℝ, A) C(unitInterval, C₀(ℝ, B)) :=
  postcomp (uniformC0Morphism (X := ℝ) H.family hH)
    (ZeroAtInftyContinuousMap.continuousMapFlipStarAlgEquiv
      (X := ℝ) (Y := unitInterval) (B := B)).toNonUnitalStarAlgHom

/-- The suspended whole family keeps the normalized pointwise values. -/
@[simp]
theorem normalizedUniformSuspensionHomotopyFamily_apply
    {φ ψ : AsymptoticMorphism A B} (H : Homotopy φ ψ)
    (hH : IsUniform H.family) (t : AsymptoticTime)
    (f : C₀(ℝ, A)) (s : unitInterval) (x : ℝ) :
    normalizedUniformSuspensionHomotopyFamily H hH t f s x =
      normalize H.family t (f x) s := by
  rw [normalizedUniformSuspensionHomotopyFamily, postcomp_apply]
  change
    (ZeroAtInftyContinuousMap.continuousMapFlipStarAlgEquiv
      (X := ℝ) (Y := unitInterval) (B := B)
      (uniformC0Morphism (X := ℝ) H.family hH t f)) s x = _
  rw [
    ZeroAtInftyContinuousMap.continuousMapFlipStarAlgEquiv_apply,
    uniformC0Morphism_apply]

namespace Homotopy

/-- A whole uniform homotopy induces an actual homotopy of its normalized
suspension representatives. Endpoint uniformity proofs determine only proof
fields; the values are fixed by the public apply formula. -/
noncomputable def normalizedUniformSuspension
    {φ ψ : AsymptoticMorphism A B} (H : Homotopy φ ψ)
    (hφ : IsUniform φ) (hψ : IsUniform ψ)
    (hH : IsUniform H.family) :
    Homotopy (AsymptoticMorphism.normalizedUniformSuspension φ hφ)
      (AsymptoticMorphism.normalizedUniformSuspension ψ hψ) where
  family := normalizedUniformSuspensionHomotopyFamily H hH
  start := by
    intro t f
    apply ZeroAtInftyContinuousMap.ext
    intro x
    rw [normalizedUniformSuspensionHomotopyFamily_apply,
      AsymptoticMorphism.normalizedUniformSuspension_apply,
      normalize_apply]
    change H.family t (f x) 0 - H.family t 0 0 = φ t (f x) - φ t 0
    rw [H.start t (f x), H.start t 0]
  finish := by
    intro t f
    apply ZeroAtInftyContinuousMap.ext
    intro x
    rw [normalizedUniformSuspensionHomotopyFamily_apply,
      AsymptoticMorphism.normalizedUniformSuspension_apply,
      normalize_apply]
    change H.family t (f x) 1 - H.family t 0 1 = ψ t (f x) - ψ t 0
    rw [H.finish t (f x), H.finish t 0]

end Homotopy

/-- The bundled construction gives the corresponding homotopy relation. -/
theorem homotopic_normalizedUniformSuspension
    {φ ψ : AsymptoticMorphism A B} (H : Homotopy φ ψ)
    (hφ : IsUniform φ) (hψ : IsUniform ψ)
    (hH : IsUniform H.family) :
    Homotopic (normalizedUniformSuspension φ hφ)
      (normalizedUniformSuspension ψ hψ) :=
  ⟨H.normalizedUniformSuspension hφ hψ hH⟩

end AsymptoticMorphism

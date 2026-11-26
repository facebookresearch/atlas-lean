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
# Suspension of uniform asymptotic morphisms

Let A,B be nonunital complex C-star algebras, T=[1,∞) and φ:A→B an asymptotic star morphism.
Assume a↦(t↦φ_t(a)) is continuous into C_b(T,B) with its supremum norm; this is IsUniform φ.
Write SA=C₀(ℝ,A), SB=C₀(ℝ,B) with their supremum norms. Its normalized suspension family is
(Sφ)_t(f)(x)=φ_t(f(x))-φ_t(0). The family Sφ:SA→SB is an asymptotic star morphism and remains
uniform. A homotopy whose whole interval-valued family is uniform gives a homotopy of these
normalized suspensions, with value H_t(f(x))(s)-H_t(0)(s). This construction is the suspension
representative used in Blackadar25.2.2.
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

/-- **Normalized suspension representative.**

Let A,B be nonunital complex C-star algebras, T=[1,∞) and φ:A→B an asymptotic star morphism.
Assume a↦(t↦φ_t(a)) is continuous into C_b(T,B) with its supremum norm; this is IsUniform φ.
Write SA=C₀(ℝ,A), SB=C₀(ℝ,B) with their supremum norms. Its normalized suspension family is
(Sφ)_t(f)(x)=φ_t(f(x))-φ_t(0). The asymptotic morphism normalizedUniformSuspension φ hφ:SA→SB
has these values and uses the supremum norm of SB for its time continuity and defects.
-/
noncomputable def normalizedUniformSuspension
    (φ : AsymptoticMorphism A B) (hφ : IsUniform φ) :
    AsymptoticMorphism C₀(ℝ, A) C₀(ℝ, B) :=
  uniformC0Morphism (X := ℝ) φ hφ

/-- **Value of the normalized suspension family.**

Let A,B be nonunital complex C-star algebras, T=[1,∞) and φ:A→B an asymptotic star morphism.
Assume a↦(t↦φ_t(a)) is continuous into C_b(T,B) with its supremum norm; this is IsUniform φ.
Write SA=C₀(ℝ,A), SB=C₀(ℝ,B) with their supremum norms. Its normalized suspension family is
(Sφ)_t(f)(x)=φ_t(f(x))-φ_t(0). For t≥1, f∈SA and x∈ℝ, normalizedUniformSuspension φ hφ t f
x=φ_t(f(x))-φ_t(0).
-/
@[simp]
theorem normalizedUniformSuspension_apply
    (φ : AsymptoticMorphism A B) (hφ : IsUniform φ)
    (t : AsymptoticTime) (f : C₀(ℝ, A)) (x : ℝ) :
    normalizedUniformSuspension φ hφ t f x = φ t (f x) - φ t 0 := by
  change uniformC0Morphism (X := ℝ) φ hφ t f x = _
  rw [uniformC0Morphism_apply, normalize_apply]

/-- **Uniformity of the normalized suspension.**

Let A,B be nonunital complex C-star algebras, T=[1,∞) and φ:A→B an asymptotic star morphism.
Assume a↦(t↦φ_t(a)) is continuous into C_b(T,B) with its supremum norm; this is IsUniform φ.
Write SA=C₀(ℝ,A), SB=C₀(ℝ,B) with their supremum norms. Its normalized suspension family is
(Sφ)_t(f)(x)=φ_t(f(x))-φ_t(0). The family normalizedUniformSuspension φ hφ is uniform:
f↦(t↦(Sφ)_t(f)) is continuous SA→C_b(T,SB) in the supremum norms.
-/
theorem isUniform_normalizedUniformSuspension
    (φ : AsymptoticMorphism A B) (hφ : IsUniform φ) :
    IsUniform (normalizedUniformSuspension φ hφ) := by
  simpa only [normalizedUniformSuspension] using
    (isUniform_uniformC0Morphism (X := ℝ) φ hφ)

/-- **Suspension formula for a zero-preserving family.**

Let A,B be nonunital complex C-star algebras, T=[1,∞) and φ:A→B an asymptotic star morphism.
Assume a↦(t↦φ_t(a)) is continuous into C_b(T,B) with its supremum norm; this is IsUniform φ.
Write SA=C₀(ℝ,A), SB=C₀(ℝ,B) with their supremum norms. Its normalized suspension family is
(Sφ)_t(f)(x)=φ_t(f(x))-φ_t(0). If φ_t(0)=0 for every t≥1, then normalizedUniformSuspension φ
hφ t f x=φ_t(f(x)).
-/
theorem normalizedUniformSuspension_apply_of_zero
    (φ : AsymptoticMorphism A B) (hφ : IsUniform φ)
    (hzero : ∀ t : AsymptoticTime, φ t 0 = 0)
    (t : AsymptoticTime) (f : C₀(ℝ, A)) (x : ℝ) :
    normalizedUniformSuspension φ hφ t f x = φ t (f x) := by
  rw [normalizedUniformSuspension_apply, hzero, sub_zero]

/-- **Interval-valued normalized suspension homotopy family.**

Let A,B be nonunital complex C-star algebras, T=[1,∞), φ,ψ:A→B asymptotic star morphisms and H
a homotopy A→C([0,1],B) with endpoints φ,ψ. Assume H.family is uniform as a map
A→C_b(T,C([0,1],B)). The normalized suspended family has values
G_t(f)(s)(x)=H_t(f(x))(s)-H_t(0)(s), for f∈C₀(ℝ,A), s∈[0,1] and x∈ℝ. The family
normalizedUniformSuspensionHomotopyFamily H hH is an asymptotic morphism
C₀(ℝ,A)→C([0,1],C₀(ℝ,B)), with the supremum norm over both interval and real variables.
-/
noncomputable def normalizedUniformSuspensionHomotopyFamily
    {φ ψ : AsymptoticMorphism A B} (H : Homotopy φ ψ)
    (hH : IsUniform H.family) :
    AsymptoticMorphism C₀(ℝ, A) C(unitInterval, C₀(ℝ, B)) :=
  postcomp (uniformC0Morphism (X := ℝ) H.family hH)
    (ZeroAtInftyContinuousMap.continuousMapFlipStarAlgEquiv
      (X := ℝ) (Y := unitInterval) (B := B)).toNonUnitalStarAlgHom

/-- **Pointwise value of the suspended homotopy family.**

Let A,B be nonunital complex C-star algebras, T=[1,∞), φ,ψ:A→B asymptotic star morphisms and H
a homotopy A→C([0,1],B) with endpoints φ,ψ. Assume H.family is uniform as a map
A→C_b(T,C([0,1],B)). The normalized suspended family has values
G_t(f)(s)(x)=H_t(f(x))(s)-H_t(0)(s), for f∈C₀(ℝ,A), s∈[0,1] and x∈ℝ. For t≥1, f∈C₀(ℝ,A),
s∈[0,1] and x∈ℝ, normalizedUniformSuspensionHomotopyFamily H hH t f s
x=H_t(f(x))(s)-H_t(0)(s).
-/
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

/-- **Homotopy of normalized suspension representatives.**

Let A,B be nonunital complex C-star algebras, T=[1,∞), φ,ψ:A→B asymptotic star morphisms and H
a homotopy A→C([0,1],B) with endpoints φ,ψ. Assume H.family is uniform as a map
A→C_b(T,C([0,1],B)). Assume also that φ and ψ are uniform. The normalized suspended family has
values G_t(f)(s)(x)=H_t(f(x))(s)-H_t(0)(s), for f∈C₀(ℝ,A), s∈[0,1] and x∈ℝ. The homotopy
Homotopy.normalizedUniformSuspension H hφ hψ hH joins normalizedUniformSuspension φ hφ to
normalizedUniformSuspension ψ hψ through this interval-valued family.
-/
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

/-- **Normalized suspensions of uniformly homotopic families are homotopic.**

Let A,B be nonunital complex C-star algebras, T=[1,∞), φ,ψ:A→B asymptotic star morphisms and H
a homotopy A→C([0,1],B) with endpoints φ,ψ. Assume H.family is uniform as a map
A→C_b(T,C([0,1],B)). Assume φ and ψ are uniform. Then normalizedUniformSuspension φ hφ and
normalizedUniformSuspension ψ hψ are homotopic as asymptotic morphisms C₀(ℝ,A)→C₀(ℝ,B).
-/
theorem homotopic_normalizedUniformSuspension
    {φ ψ : AsymptoticMorphism A B} (H : Homotopy φ ψ)
    (hφ : IsUniform φ) (hψ : IsUniform ψ)
    (hH : IsUniform H.family) :
    Homotopic (normalizedUniformSuspension φ hφ)
      (normalizedUniformSuspension ψ hψ) :=
  ⟨H.normalizedUniformSuspension hφ hψ hH⟩

end AsymptoticMorphism

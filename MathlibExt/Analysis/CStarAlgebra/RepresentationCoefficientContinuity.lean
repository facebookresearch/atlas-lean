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

public import MathlibExt.Analysis.CStarAlgebra.RepresentationCoefficient

/-!
# Original representation coefficients are continuous in their Hilbert vectors

The existing coefficient laws and norm bound construct the actual bounded
linear map in its first vector and bounded conjugate-linear map in its
second vector. Their original coefficient values prove the two continuity
statements, without a given coefficient norm or continuity certificate.
These continuity facts extend normal membership from actual dense vectors.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MathlibExt.Analysis.CStarAlgebra

noncomputable section

universe u v

variable {A : Type u} [CStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Continuity in the first coefficient vector.** Let `A` be a unital complex C*-algebra, `H` a
complete complex Hilbert space, and `ρ : A → B(H)` a unital complex star representation. For a fixed
`h ∈ H`, the map taking `g` to the continuous functional `a ↦ ⟨h,ρ(a)g⟩` is norm-continuous from `H`
to the continuous dual of `A`. -/
theorem representationCoefficient_continuous_left
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (h : H) :
    Continuous (fun g : H => representationCoefficient ρ g h) := by
  let L : H →ₗ[ℂ] StrongDual ℂ A :=
    { toFun := fun g => representationCoefficient ρ g h
      map_add' := fun g₁ g₂ => representationCoefficient_add_left ρ g₁ g₂ h
      map_smul' := fun c g => representationCoefficient_smul_left ρ c g h }
  have hbound (g : H) : ‖L g‖ ≤ ‖h‖ * ‖g‖ := by
    exact (norm_representationCoefficient_le ρ g h).trans_eq (mul_comm ‖g‖ ‖h‖)
  exact (L.mkContinuous ‖h‖ hbound).continuous

/-- **Continuity in the second coefficient vector.** Let `A` be a unital complex C*-algebra, `H` a
complete complex Hilbert space, and `ρ : A → B(H)` a unital complex star representation. For a fixed
`g ∈ H`, the map taking `h` to the continuous functional `a ↦ ⟨h,ρ(a)g⟩` is norm-continuous from `H`
to the continuous dual of `A`. -/
theorem representationCoefficient_continuous_right
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (g : H) :
    Continuous (fun h : H => representationCoefficient ρ g h) := by
  let L : H →ₗ⋆[ℂ] StrongDual ℂ A :=
    { toFun := fun h => representationCoefficient ρ g h
      map_add' := fun h₁ h₂ => representationCoefficient_add_right ρ g h₁ h₂
      map_smul' := fun c h => representationCoefficient_smul_right ρ c g h }
  have hbound (h : H) : ‖L h‖ ≤ ‖g‖ * ‖h‖ := norm_representationCoefficient_le ρ g h
  exact (L.mkContinuous ‖g‖ hbound).continuous

end

end MathlibExt.Analysis.CStarAlgebra

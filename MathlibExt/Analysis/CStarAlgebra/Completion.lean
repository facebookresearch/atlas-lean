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

public import MathlibExt.Analysis.Normed.StarCompletion
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Module.Completion

/-!
# C-star structure on the completion of an incomplete C-star ring

The ordinary uniform completion already owns the canonical ring, norm, scalar
and algebra structures. This file extends the isometric involution and packages
the resulting complete C-star algebra as an explicit locally activated value.
No global instance is registered.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace CStarAlgebra

universe uA

private theorem completionMapStar_involutive
    (A : Type uA) [NormedRing A] [StarRing A] [CStarRing A]
    (x : UniformSpace.Completion A) :
    UniformSpace.Completion.map (star : A → A)
        (UniformSpace.Completion.map (star : A → A) x) = x := by
  exact (UniformSpace.Completion.completionStarRing A).star_involutive x

private theorem completionMapStar_add
    (A : Type uA) [NormedRing A] [StarRing A] [CStarRing A]
    (x y : UniformSpace.Completion A) :
    UniformSpace.Completion.map (star : A → A) (x + y) =
      UniformSpace.Completion.map (star : A → A) x +
        UniformSpace.Completion.map (star : A → A) y := by
  exact (UniformSpace.Completion.completionStarRing A).star_add x y

private theorem completionMapStar_mul
    (A : Type uA) [NormedRing A] [StarRing A] [CStarRing A]
    (x y : UniformSpace.Completion A) :
    UniformSpace.Completion.map (star : A → A) (x * y) =
      UniformSpace.Completion.map (star : A → A) y *
        UniformSpace.Completion.map (star : A → A) x := by
  exact (UniformSpace.Completion.completionStarRing A).star_mul x y

private theorem completionMapStar_smul
    (A : Type uA) [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [StarModule ℂ A] [CStarRing A]
    (c : ℂ) (x : UniformSpace.Completion A) :
    UniformSpace.Completion.map (star : A → A) (c • x) =
      star c • UniformSpace.Completion.map (star : A → A) x := by
  exact (UniformSpace.Completion.completionStarModule A).star_smul c x

private theorem completionMapStar_norm_mul_self_le
    (A : Type uA) [NormedRing A] [StarRing A] [CStarRing A]
    (x : UniformSpace.Completion A) :
    ‖x‖ * ‖x‖ ≤
      ‖UniformSpace.Completion.map (star : A → A) x * x‖ := by
  let s : UniformSpace.Completion A → UniformSpace.Completion A :=
    UniformSpace.Completion.map (star : A → A)
  have hstar : Continuous s :=
    UniformSpace.Completion.continuous_map
  change ‖x‖ * ‖x‖ ≤ ‖s x * x‖
  refine UniformSpace.Completion.induction_on
    (p := fun z => ‖z‖ * ‖z‖ ≤ ‖s z * z‖) x
    (isClosed_le
      (continuous_norm.mul continuous_norm)
      ((hstar.mul continuous_id).norm)) ?_
  intro a
  dsimp only [s]
  rw [UniformSpace.Completion.map_coe star_isometry.uniformContinuous,
    ← UniformSpace.Completion.coe_mul]
  simpa only [UniformSpace.Completion.norm_coe] using
    CStarRing.norm_mul_self_le a

/-- **C*-algebra structure on a uniform completion.** Let `A` be a normed unital complex algebra with a
ring involution compatible with complex scalar multiplication and satisfying the C*-identity `‖a* a‖
= ‖a‖²`. Its uniform completion carries a unital complex C*-algebra structure extending the
algebraic operations and norm of `A`; completeness of `A` is not required. -/
@[instance_reducible]
noncomputable def completionCStarAlgebra
    (A : Type uA) [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [StarModule ℂ A] [CStarRing A] :
    CStarAlgebra (UniformSpace.Completion A) where
  toNormedRing := inferInstance
  toCompleteSpace := inferInstance
  toNormedAlgebra := { norm_smul_le := norm_smul_le }
  star := UniformSpace.Completion.map (star : A → A)
  star_involutive x := by
    exact completionMapStar_involutive A x
  star_add x y := by
    exact completionMapStar_add A x y
  star_mul x y := by
    exact completionMapStar_mul A x y
  star_smul c x := by
    exact completionMapStar_smul A c x
  norm_mul_self_le x := by
    exact completionMapStar_norm_mul_self_le A x

/-- **Involution on the completion extends the original involution.** Let `A` be a normed unital complex
algebra with scalar-compatible ring involution and the C*-identity. For its canonical map `ι` into
the uniform C*-completion and every `x ∈ A`, `(ι(x))* = ι(x*)`. -/
theorem completionCStarAlgebra_star_coe
    (A : Type uA) [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [StarModule ℂ A] [CStarRing A] (x : A) :
    let _ : CStarAlgebra (UniformSpace.Completion A) :=
      completionCStarAlgebra A
    star (x : UniformSpace.Completion A) =
      (star x : A) := by
  change UniformSpace.Completion.map (star : A → A)
    (x : UniformSpace.Completion A) = (star x : A)
  exact UniformSpace.Completion.map_coe star_isometry.uniformContinuous x

#print axioms completionCStarAlgebra
#print axioms completionCStarAlgebra_star_coe

end CStarAlgebra

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

public import MathlibExt.Analysis.Normed.Algebra.NonUnitalStarCompletion
public import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# C-star structure on a nonunital completion

This file adds the C-star involution to the existing canonical nonunital
normed-ring completion. Multiplication, scalar compatibility, the stock norm,
and the dense canonical inclusion are reused from
`Analysis.Normed.Algebra.NonUnitalCompletion`.

The factory is explicit and locally activated. No global completion instance is
registered, and no unit, transported norm, chosen model, or source completeness
is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace CStarAlgebra

universe uA

private theorem completionNonUnitalMapStar_involutive
    (A : Type uA) [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    (x : UniformSpace.Completion A) :
    let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
      UniformSpace.Completion.nonUnitalCompletionNormedRing A
    UniformSpace.Completion.map (star : A → A)
        (UniformSpace.Completion.map (star : A → A) x) = x := by
  let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
    UniformSpace.Completion.nonUnitalCompletionNormedRing A
  let s : UniformSpace.Completion A → UniformSpace.Completion A :=
    UniformSpace.Completion.map (star : A → A)
  have hstar : Continuous s := UniformSpace.Completion.continuous_map
  change s (s x) = x
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (hstar.comp hstar) continuous_id) ?_
  intro a
  dsimp only [s]
  rw [UniformSpace.Completion.map_coe star_isometry.uniformContinuous,
    UniformSpace.Completion.map_coe star_isometry.uniformContinuous,
    star_star]

private theorem completionNonUnitalMapStar_add
    (A : Type uA) [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    (x y : UniformSpace.Completion A) :
    let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
      UniformSpace.Completion.nonUnitalCompletionNormedRing A
    UniformSpace.Completion.map (star : A → A) (x + y) =
      UniformSpace.Completion.map (star : A → A) x +
        UniformSpace.Completion.map (star : A → A) y := by
  let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
    UniformSpace.Completion.nonUnitalCompletionNormedRing A
  let s : UniformSpace.Completion A → UniformSpace.Completion A :=
    UniformSpace.Completion.map (star : A → A)
  have hstar : Continuous s := UniformSpace.Completion.continuous_map
  change s (x + y) = s x + s y
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_eq
      (hstar.comp (continuous_fst.add continuous_snd))
      ((hstar.comp continuous_fst).add (hstar.comp continuous_snd))) ?_
  intro a b
  dsimp only [s]
  rw [← UniformSpace.Completion.coe_add,
    UniformSpace.Completion.map_coe star_isometry.uniformContinuous,
    UniformSpace.Completion.map_coe star_isometry.uniformContinuous,
    UniformSpace.Completion.map_coe star_isometry.uniformContinuous,
    star_add]
  exact UniformSpace.Completion.coe_add (star a) (star b)

private theorem completionNonUnitalMapStar_mul
    (A : Type uA) [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    (x y : UniformSpace.Completion A) :
    let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
      UniformSpace.Completion.nonUnitalCompletionNormedRing A
    UniformSpace.Completion.map (star : A → A) (x * y) =
      UniformSpace.Completion.map (star : A → A) y *
        UniformSpace.Completion.map (star : A → A) x := by
  let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
    UniformSpace.Completion.nonUnitalCompletionNormedRing A
  let s : UniformSpace.Completion A → UniformSpace.Completion A :=
    UniformSpace.Completion.map (star : A → A)
  have hstar : Continuous s := UniformSpace.Completion.continuous_map
  change s (x * y) = s y * s x
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_eq
      (hstar.comp (continuous_fst.mul continuous_snd))
      ((hstar.comp continuous_snd).mul (hstar.comp continuous_fst))) ?_
  intro a b
  dsimp only [s]
  rw [← UniformSpace.Completion.nonUnitalCompletion_coe_mul A,
    UniformSpace.Completion.map_coe star_isometry.uniformContinuous,
    UniformSpace.Completion.map_coe star_isometry.uniformContinuous,
    UniformSpace.Completion.map_coe star_isometry.uniformContinuous,
    star_mul]
  exact UniformSpace.Completion.nonUnitalCompletion_coe_mul A (star b) (star a)

private theorem completionNonUnitalMapStar_smul
    (A : Type uA) [NonUnitalNormedRing A] [NormedSpace ℂ A]
    [StarRing A] [StarModule ℂ A] [CStarRing A]
    (c : ℂ) (x : UniformSpace.Completion A) :
    let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
      UniformSpace.Completion.nonUnitalCompletionNormedRing A
    UniformSpace.Completion.map (star : A → A) (c • x) =
      star c • UniformSpace.Completion.map (star : A → A) x := by
  let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
    UniformSpace.Completion.nonUnitalCompletionNormedRing A
  let s : UniformSpace.Completion A → UniformSpace.Completion A :=
    UniformSpace.Completion.map (star : A → A)
  have hstar : Continuous s := UniformSpace.Completion.continuous_map
  change s (c • x) = star c • s x
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq
      (hstar.comp (continuous_const_smul c))
      (hstar.const_smul (star c))) ?_
  intro a
  dsimp only [s]
  rw [← UniformSpace.Completion.coe_smul,
    UniformSpace.Completion.map_coe star_isometry.uniformContinuous,
    UniformSpace.Completion.map_coe star_isometry.uniformContinuous,
    star_smul]
  exact UniformSpace.Completion.coe_smul (star c) (star a)

private theorem completionNonUnitalMapStar_norm_mul_self_le
    (A : Type uA) [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    (x : UniformSpace.Completion A) :
    let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
      UniformSpace.Completion.nonUnitalCompletionNormedRing A
    ‖x‖ * ‖x‖ ≤
      ‖UniformSpace.Completion.map (star : A → A) x * x‖ := by
  let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
    UniformSpace.Completion.nonUnitalCompletionNormedRing A
  let s : UniformSpace.Completion A → UniformSpace.Completion A :=
    UniformSpace.Completion.map (star : A → A)
  have hstar : Continuous s := UniformSpace.Completion.continuous_map
  change ‖x‖ * ‖x‖ ≤ ‖s x * x‖
  refine UniformSpace.Completion.induction_on x
    (isClosed_le
      (continuous_norm.mul continuous_norm)
      ((hstar.mul continuous_id).norm)) ?_
  intro a
  dsimp only [s]
  rw [UniformSpace.Completion.map_coe star_isometry.uniformContinuous,
    ← UniformSpace.Completion.nonUnitalCompletion_coe_mul]
  simpa only [UniformSpace.Completion.norm_coe] using
    CStarRing.norm_mul_self_le a

/-- **Nonunital C*-completion.** Let `A` be a nonunital normed complex algebra with a ring involution
compatible with complex scalars and satisfying `‖a* a‖ = ‖a‖²`; `A` need not be complete. Its
uniform completion carries a nonunital complex C*-algebra structure with the extended norm,
multiplication, complex scalar action, and involution. -/
@[instance_reducible]
noncomputable def completionNonUnitalCStarAlgebra
    (A : Type uA)
    [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    [NormedSpace ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [StarModule ℂ A] :
    NonUnitalCStarAlgebra (UniformSpace.Completion A) := by
  let completionRing : NonUnitalNormedRing (UniformSpace.Completion A) :=
    UniformSpace.Completion.nonUnitalCompletionNormedRing A
  let _ : NonUnitalNormedRing (UniformSpace.Completion A) := completionRing
  let completionTower : IsScalarTower ℂ (UniformSpace.Completion A)
      (UniformSpace.Completion A) :=
    UniformSpace.Completion.nonUnitalCompletionIsScalarTower A
  let _ : IsScalarTower ℂ (UniformSpace.Completion A)
      (UniformSpace.Completion A) := completionTower
  let completionComm : SMulCommClass ℂ (UniformSpace.Completion A)
      (UniformSpace.Completion A) :=
    UniformSpace.Completion.nonUnitalCompletionSMulCommClass A
  let _ : SMulCommClass ℂ (UniformSpace.Completion A)
      (UniformSpace.Completion A) := completionComm
  exact
    { toNonUnitalNormedRing := completionRing
      __ : CompleteSpace (UniformSpace.Completion A) := inferInstance
      __ : NormedSpace ℂ (UniformSpace.Completion A) := inferInstance
      __ : IsScalarTower ℂ (UniformSpace.Completion A)
          (UniformSpace.Completion A) := completionTower
      __ : SMulCommClass ℂ (UniformSpace.Completion A)
          (UniformSpace.Completion A) := completionComm
      star := UniformSpace.Completion.map (star : A → A)
      star_involutive := by exact completionNonUnitalMapStar_involutive A
      star_add := by exact completionNonUnitalMapStar_add A
      star_mul := by exact completionNonUnitalMapStar_mul A
      star_smul := by exact completionNonUnitalMapStar_smul A
      norm_mul_self_le := by exact completionNonUnitalMapStar_norm_mul_self_le A }

/-- **Involution on a nonunital C*-completion.** Let `A` be a nonunital normed complex algebra with a
ring involution compatible with complex scalars and satisfying `‖a* a‖ = ‖a‖²`; `A` need not be
complete. For the canonical dense map `ι` into its uniform completion and every `a ∈ A`, `(ι(a))* =
ι(a*)`. -/
theorem completionNonUnitalCStarAlgebra_star_coe
    (A : Type uA)
    [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    [NormedSpace ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [StarModule ℂ A] (a : A) :
    let _ : NonUnitalCStarAlgebra (UniformSpace.Completion A) :=
      completionNonUnitalCStarAlgebra A
    star (a : UniformSpace.Completion A) =
      (star a : A) := by
  let _ : NonUnitalCStarAlgebra (UniformSpace.Completion A) :=
    completionNonUnitalCStarAlgebra A
  change UniformSpace.Completion.map (star : A → A)
    (a : UniformSpace.Completion A) = (star a : A)
  exact UniformSpace.Completion.map_coe star_isometry.uniformContinuous a

end CStarAlgebra

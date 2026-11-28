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

public import MathlibExt.Analysis.Normed.Algebra.NonUnitalStarCompletion.Hom

/-!
# Norm and metric preservation under completion

Let R be a monoid acting distributively on A and B, with uniformly continuous
fixed-scalar maps. Let A be a nonunital seminormed ring with continuous star.
Let B be a nonunital nonassociative ring with a norm and a complete T₀
pseudometric uniform additive-group structure, continuous multiplication and
continuous star. Assume dist(x,y) = ‖-x+y‖ in B.

A continuous R-equivariant nonunital star homomorphism φ : A → B that preserves
norms extends to the normed star-ring completion of A. Its extension Γ
preserves norms, is an isometry, and is injective.
-/

@[expose] public section

noncomputable section

namespace NonUnitalStarAlgHom

open UniformSpace.Completion

universe uR uA uB

variable {R : Type uR} {A : Type uA} {B : Type uB}
variable [Monoid R]
variable [NonUnitalSeminormedRing A] [StarRing A] [ContinuousStar A]
variable [DistribMulAction R A] [UniformContinuousConstSMul R A]
variable [NonUnitalNonAssocRing B] [Norm B] [PseudoMetricSpace B]
variable [IsUniformAddGroup B] [CompleteSpace B] [T0Space B]
variable [ContinuousMul B] [Star B] [ContinuousStar B]
variable [DistribMulAction R B] [UniformContinuousConstSMul R B]

/-- **Norm-preserving completion extension is an injective isometry.** Let R be a monoid with
distributive actions on A,B whose fixed-scalar maps are uniformly continuous. Let A be a
nonunital seminormed ring with continuous star, and B a nonunital nonassociative ring with
a norm, a complete T₀ pseudometric uniform additive-group structure, continuous
multiplication and continuous star. Assume dist(x,y) = ‖-x+y‖ for all x,y : B. For a
continuous R-equivariant nonunital star homomorphism φ : A → B with ‖φ(a)‖ = ‖a‖ for all
a, the completion extension Γ preserves every norm, is an isometry, and is injective. -/
theorem fromCompletion_norm_isometry
    (hDistB : ∀ x y : B, dist x y = ‖-x + y‖)
    (φ : A →⋆ₙₐ[R] B) (hφ : Continuous φ)
    (hNorm : ∀ a : A, ‖φ a‖ = ‖a‖) :
    let C := UniformSpace.Completion A;
    let rC : NonUnitalNormedRing C := nonUnitalCompletionNormedRing A;
    letI : NonUnitalNormedRing C := rC;
    let rS : StarRing C := nonUnitalCompletionStarRing A;
    letI : StarRing C := rS;
    let mC : DistribMulAction R C := inferInstance;
    letI : DistribMulAction R C := mC;
    let Γ : C →⋆ₙₐ[R] B := fromCompletion φ hφ;
    (∀ x : C, ‖Γ x‖ = ‖x‖) ∧ Isometry Γ ∧ Function.Injective Γ := by
  let C := UniformSpace.Completion A
  let rC : NonUnitalNormedRing C := nonUnitalCompletionNormedRing A
  let : NonUnitalNormedRing C := rC
  let rS : StarRing C := nonUnitalCompletionStarRing A
  let : StarRing C := rS
  let mC : DistribMulAction R C := inferInstance
  let : DistribMulAction R C := mC
  let Γ : C →⋆ₙₐ[R] B := fromCompletion φ hφ
  change (∀ x : C, ‖Γ x‖ = ‖x‖) ∧ Isometry Γ ∧ Function.Injective Γ
  have hIsoφ : Isometry (φ : A → B) := Isometry.of_dist_eq fun a b => by
    calc
      dist (φ a) (φ b) = ‖-φ a + φ b‖ := hDistB _ _
      _ = ‖φ (-a + b)‖ := by rw [map_add, map_neg]
      _ = ‖-a + b‖ := hNorm _
      _ = dist a b := (NonUnitalSeminormedRing.dist_eq a b).symm
  let φa : A →+ B := AddMonoidHom.ofClass φ
  have hφa : Continuous φa := hφ
  have hFun : (Γ : C → B) = UniformSpace.Completion.extension (φ : A → B) := by
    calc
      (Γ : C → B) = (φa.extension hφa : C → B) := coe_fromCompletion φ hφ
      _ = UniformSpace.Completion.extension (φ : A → B) := rfl
  have hIsoΓ : Isometry Γ := by
    rw [hFun]
    exact hIsoφ.completion_extension
  refine ⟨?_, hIsoΓ, hIsoΓ.injective⟩
  intro x
  have hZero : Γ (0 : C) = (0 : B) := map_zero Γ
  calc
    ‖Γ x‖ = dist (0 : B) (Γ x) := by rw [hDistB, neg_zero, zero_add]
    _ = dist (0 : C) x := by simpa only [hZero] using hIsoΓ.dist_eq (0 : C) x
    _ = ‖x‖ := by rw [NonUnitalNormedRing.dist_eq, neg_zero, zero_add]

end NonUnitalStarAlgHom

end

end

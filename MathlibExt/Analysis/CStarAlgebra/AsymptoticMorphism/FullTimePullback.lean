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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Correspondence
public import MathlibExt.Analysis.CStarAlgebra.Pullback
public import MathlibExt.Analysis.CStarAlgebra.Extension.Basic

/-!
# The full-time pullback extension of an asymptotic morphism

A raw asymptotic morphism determines a homomorphism into the actual closed-ray
asymptotic algebra. Its pullback along the bounded-function quotient is a
genuine C-star extension with full C0 kernel. No coefficient-wise linearity,
faithfulness, separability, uniformity or unitality is assumed.

The middle algebra and norm are the existing closed pullback. The quotient
C-star dictionary is the explicit existing factory, not a new global instance.
The orbit section is only set-theoretic. Evaluation gives ordinary star
homomorphisms and is point-norm continuous in time.

Reference: Blackadar, K-Theory for Operator Algebras (1998), §25.6, the extension
preceding Proposition 25.6.2. The E-theory inverse, homotopy comparison and
universal property are not asserted here.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ZeroAtInfty BoundedContinuousFunction

noncomputable section

namespace AsymptoticMorphism

universe uA uB

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

attribute [local instance] _root_.AsymptoticAlgebra.cStarAlgebra

/-- The actual closed full-time pullback, with the fixed quotient dictionary.
Its C-star structure and norm are inherited from the existing pullback. -/
abbrev FullTimePullback (φ : AsymptoticMorphism A B) : Type (max uA uB) :=
  letI : NonUnitalCStarAlgebra (AsymptoticAlgebra B) :=
    _root_.AsymptoticAlgebra.cStarAlgebra B
  ↥(NonUnitalCStarPullback.Pullback (toHom φ)
    (_root_.AsymptoticAlgebra.quotientMap B))

namespace FullTimePullback

variable (φ : AsymptoticMorphism A B)

/-- Projection of the full-time pullback onto the coefficient algebra. -/
def projection : FullTimePullback φ →⋆ₙₐ[ℂ] A :=
  NonUnitalCStarPullback.fstHom (toHom φ)
    (_root_.AsymptoticAlgebra.quotientMap B)

/-- The actual bounded-function coordinate of a pullback element. -/
def orbitProjection : FullTimePullback φ →⋆ₙₐ[ℂ] (AsymptoticTime →ᵇ B) :=
  NonUnitalCStarPullback.sndHom (toHom φ)
    (_root_.AsymptoticAlgebra.quotientMap B)

/-- Projection has the unchanged first-coordinate value. -/
theorem projection_apply (d : FullTimePullback φ) :
    projection φ d = d.val.1 :=
  rfl

/-- The bounded-function coordinate has its unchanged pointwise data. -/
theorem orbitProjection_apply (d : FullTimePullback φ) :
    orbitProjection φ d = d.val.2 :=
  rfl

/-- The literal compatibility equation defining the closed pullback. -/
theorem condition (d : FullTimePullback φ) :
    toHom φ (projection φ d) =
      _root_.AsymptoticAlgebra.quotientMap B (orbitProjection φ d) :=
  NonUnitalCStarPullback.condition (toHom φ)
    (_root_.AsymptoticAlgebra.quotientMap B) d

/-- The raw orbit is a deterministic set section, not a homomorphism section. -/
def setSection (a : A) : FullTimePullback φ :=
  NonUnitalCStarPullback.mk (toHom φ)
    (_root_.AsymptoticAlgebra.quotientMap B)
    a (orbitBCF φ a) (toHom_apply φ a)

/-- The orbit section is a right inverse of the actual projection. -/
@[simp]
theorem projection_setSection (a : A) :
    projection φ (setSection φ a) = a :=
  rfl

/-- The section retains the complete original bounded time orbit. -/
@[simp]
theorem orbitProjection_setSection (a : A) :
    orbitProjection φ (setSection φ a) = orbitBCF φ a :=
  rfl

/-- Include full C0 on the closed ray into the actual kernel.
No vanishing-at-one condition is imposed on the input. -/
def kernelInclusion : C₀(AsymptoticTime, B) →⋆ₙₐ[ℂ] FullTimePullback φ where
  toFun f :=
    NonUnitalCStarPullback.mk (toHom φ)
      (_root_.AsymptoticAlgebra.quotientMap B) 0 f.toBCF
      ((map_zero (toHom φ)).trans
        (_root_.AsymptoticAlgebra.quotientMap_toBCF f).symm)
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' := by
    intro f g
    apply NonUnitalCStarPullback.ext (toHom φ)
      (_root_.AsymptoticAlgebra.quotientMap B)
    · change (0 : A) = 0 + 0
      exact (zero_add 0).symm
    · change (f + g).toBCF = f.toBCF + g.toBCF
      apply BoundedContinuousFunction.ext
      intro t
      rfl
  map_smul' := by
    intro z f
    apply NonUnitalCStarPullback.ext (toHom φ)
      (_root_.AsymptoticAlgebra.quotientMap B)
    · change (0 : A) = z • 0
      exact (smul_zero z).symm
    · change (z • f).toBCF = z • f.toBCF
      apply BoundedContinuousFunction.ext
      intro t
      rfl
  map_mul' := by
    intro f g
    apply NonUnitalCStarPullback.ext (toHom φ)
      (_root_.AsymptoticAlgebra.quotientMap B)
    · change (0 : A) = 0 * 0
      exact (zero_mul 0).symm
    · change (f * g).toBCF = f.toBCF * g.toBCF
      apply BoundedContinuousFunction.ext
      intro t
      rfl
  map_star' := by
    intro f
    apply NonUnitalCStarPullback.ext (toHom φ)
      (_root_.AsymptoticAlgebra.quotientMap B)
    · change (0 : A) = star 0
      exact (star_zero A).symm
    · change (star f).toBCF = star f.toBCF
      apply BoundedContinuousFunction.ext
      intro t
      rfl

/-- Every included full C0 function is in the kernel of the projection. -/
@[simp]
theorem projection_kernelInclusion (f : C₀(AsymptoticTime, B)) :
    projection φ (kernelInclusion φ f) = 0 :=
  rfl

/-- Inclusion retains the complete original bounded-function coordinate. -/
@[simp]
theorem orbitProjection_kernelInclusion (f : C₀(AsymptoticTime, B)) :
    orbitProjection φ (kernelInclusion φ f) = f.toBCF :=
  rfl

/-- The full C0 kernel inclusion is injective. -/
theorem kernelInclusion_injective : Function.Injective (kernelInclusion φ) := by
  intro f g h
  apply ZeroAtInftyContinuousMap.toBCF_injective AsymptoticTime B
  have hcoord := congrArg (orbitProjection φ) h
  simpa only [orbitProjection_kernelInclusion] using hcoord

/-- The deterministic orbit section proves actual quotient surjectivity. -/
theorem projection_surjective : Function.Surjective (projection φ) :=
  fun a => ⟨setSection φ a, projection_setSection φ a⟩

/-- The actual sequence with full closed-ray C0 kernel is exact. -/
theorem exact : Function.Exact (kernelInclusion φ) (projection φ) := by
  intro d
  constructor
  · intro hd
    have hq :
        _root_.AsymptoticAlgebra.quotientMap B (orbitProjection φ d) = 0 := by
      rw [← condition φ d, hd, map_zero]
    have hmem :
        orbitProjection φ d ∈
          (BoundedContinuousFunction.vanishingIdeal AsymptoticTime B :
            Set (AsymptoticTime →ᵇ B)) :=
      (_root_.AsymptoticAlgebra.mem_vanishingIdeal_iff (orbitProjection φ d)).2
        ((_root_.AsymptoticAlgebra.quotientMap_eq_zero_iff
          (orbitProjection φ d)).1 hq)
    rw [BoundedContinuousFunction.vanishingIdeal_carrier AsymptoticTime B] at hmem
    obtain ⟨f, hf⟩ := hmem
    refine ⟨f, ?_⟩
    apply NonUnitalCStarPullback.ext (toHom φ)
      (_root_.AsymptoticAlgebra.quotientMap B)
    · change projection φ (kernelInclusion φ f) = projection φ d
      rw [projection_kernelInclusion, hd]
    · change orbitProjection φ (kernelInclusion φ f) = orbitProjection φ d
      exact (orbitProjection_kernelInclusion φ f).trans hf
  · rintro ⟨f, rfl⟩
    exact projection_kernelInclusion φ f

/-- The normalized extension has the actual full-time pullback as its middle. -/
def extension : CStarExtension A C₀(AsymptoticTime, B) :=
  CStarExtension.ofExact (kernelInclusion φ) (projection φ)
    (kernelInclusion_injective φ) (projection_surjective φ) (exact φ)

/-- Normalization retains the actual middle carrier, not a replacement algebra. -/
theorem extension_middle :
    (extension φ).Middle = FullTimePullback φ :=
  rfl

/-- The normalized inclusion has the original full C0 inclusion value. -/
theorem extension_inclusion_apply (f : C₀(AsymptoticTime, B)) :
    (extension φ).inclusion f = kernelInclusion φ f :=
  CStarExtension.ofExact_inclusion_apply (kernelInclusion φ) (projection φ)
    (kernelInclusion_injective φ) (projection_surjective φ) (exact φ) f

/-- The normalized quotient has the original coefficient-projection value. -/
theorem extension_quotient_apply (d : FullTimePullback φ) :
    (extension φ).quotient d = projection φ d :=
  CStarExtension.ofExact_quotient_apply (kernelInclusion φ) (projection φ)
    (kernelInclusion_injective φ) (projection_surjective φ) (exact φ) d

/-- Evaluation at an actual time is an ordinary nonunital star homomorphism. -/
def evaluation (t : AsymptoticTime) : FullTimePullback φ →⋆ₙₐ[ℂ] B where
  toFun d := orbitProjection φ d t
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

/-- Ordinary evaluation uses the unchanged bounded-function coordinate. -/
@[simp]
theorem evaluation_apply (t : AsymptoticTime) (d : FullTimePullback φ) :
    evaluation φ t d = orbitProjection φ d t :=
  rfl

/-- Evaluating the set section recovers the original possibly nonlinear value. -/
theorem evaluation_setSection (t : AsymptoticTime) (a : A) :
    evaluation φ t (setSection φ a) = φ t a := by
  rw [evaluation_apply, orbitProjection_setSection, orbitBCF_apply]

/-- Full C0 inclusion allows its original evaluation at every time, including one. -/
theorem evaluation_kernelInclusion
    (t : AsymptoticTime) (f : C₀(AsymptoticTime, B)) :
    evaluation φ t (kernelInclusion φ f) = f t := by
  rw [evaluation_apply, orbitProjection_kernelInclusion]
  rfl

/-- Evaluation is point-norm continuous in time for each fixed pullback element. -/
theorem evaluation_continuous (d : FullTimePullback φ) :
    Continuous (fun t : AsymptoticTime => evaluation φ t d) := by
  have hd : Continuous (fun t : AsymptoticTime => orbitProjection φ d t) :=
    (orbitProjection φ d).continuous
  simpa only [evaluation_apply] using hd

end FullTimePullback

end AsymptoticMorphism

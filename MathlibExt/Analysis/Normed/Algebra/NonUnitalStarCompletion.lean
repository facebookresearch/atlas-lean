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

public import MathlibExt.Analysis.Normed.Algebra.NonUnitalCompletion
public import Mathlib.Topology.Algebra.Star

/-!
# Continuous star on the canonical nonunital ring completion

A continuous source star is additive, hence uniformly continuous. Its
ordinary completion map supplies the involution on the existing nonunital
normed-ring completion. The original completed addition, multiplication,
uniformity and norm remain unchanged.

The factories are explicit and locally activated. No source completeness,
separatedness, unit, scalar action, C-star identity or norm-star isometry is
assumed, and no global completion instance is registered.
-/

@[expose] public section

noncomputable section

namespace UniformSpace.Completion

universe uA

/-- **Involution on a nonunital uniform completion.** Let `A` be a nonunital seminormed ring with a
continuous ring involution. The source involution extends to a ring involution on the uniform
completion, with its induced nonunital normed ring operations. -/
@[instance_reducible]
noncomputable def nonUnitalCompletionStarRing
    (A : Type uA) [NonUnitalSeminormedRing A]
    [StarRing A] [ContinuousStar A] :
    let rC : NonUnitalNormedRing (UniformSpace.Completion A) :=
      nonUnitalCompletionNormedRing A;
    @StarRing (UniformSpace.Completion A)
      (rC.toNonUnitalRing.toNonUnitalSemiring.toNonUnitalNonAssocSemiring) := by
  let C := UniformSpace.Completion A
  let rC : NonUnitalNormedRing C := nonUnitalCompletionNormedRing A
  letI : NonUnitalNormedRing C := rC
  letI : NonUnitalNonAssocSemiring C :=
    rC.toNonUnitalRing.toNonUnitalSemiring.toNonUnitalNonAssocSemiring
  change StarRing C
  let fStar : A →+ A := (starAddEquiv : A ≃+ A).toAddMonoidHom
  have hUC : UniformContinuous (star : A → A) :=
    uniformContinuous_addMonoidHom_of_continuous (f := fStar)
      (show Continuous fStar from continuous_star)
  let s : C → C := UniformSpace.Completion.map (star : A → A)
  have hs : Continuous s := UniformSpace.Completion.continuous_map
  have hInv : Function.Involutive s := by
    intro x
    refine UniformSpace.Completion.induction_on
      (α := A) (p := fun x : C => s (s x) = x) x
      (isClosed_eq (hs.comp hs) continuous_id) ?_
    intro a
    change UniformSpace.Completion.map (star : A → A)
      (UniformSpace.Completion.map (star : A → A) (a : C)) = (a : C)
    rw [UniformSpace.Completion.map_coe hUC,
      UniformSpace.Completion.map_coe hUC, star_star]
  have hAdd : ∀ x y : C, s (x + y) = s x + s y := by
    intro x y
    have hLeft : Continuous (fun p : C × C => s (p.1 + p.2)) :=
      hs.comp (continuous_fst.add continuous_snd)
    have hRight : Continuous (fun p : C × C => s p.1 + s p.2) :=
      (hs.comp continuous_fst).add (hs.comp continuous_snd)
    refine UniformSpace.Completion.induction_on₂
      (α := A) (β := A) (p := fun x y : C => s (x + y) = s x + s y)
      x y (isClosed_eq hLeft hRight) ?_
    intro a b
    change UniformSpace.Completion.map (star : A → A)
      ((a : C) + (b : C)) =
        UniformSpace.Completion.map (star : A → A) (a : C) +
          UniformSpace.Completion.map (star : A → A) (b : C)
    rw [← UniformSpace.Completion.coe_add,
      UniformSpace.Completion.map_coe hUC,
      UniformSpace.Completion.map_coe hUC,
      UniformSpace.Completion.map_coe hUC, star_add]
    exact UniformSpace.Completion.coe_add (star a) (star b)
  have hMul : ∀ x y : C, s (x * y) = s y * s x := by
    intro x y
    have hLeft : Continuous (fun p : C × C => s (p.1 * p.2)) :=
      hs.comp (continuous_fst.mul continuous_snd)
    have hRight : Continuous (fun p : C × C => s p.2 * s p.1) :=
      (hs.comp continuous_snd).mul (hs.comp continuous_fst)
    refine UniformSpace.Completion.induction_on₂
      (α := A) (β := A) (p := fun x y : C => s (x * y) = s y * s x)
      x y (isClosed_eq hLeft hRight) ?_
    intro a b
    change UniformSpace.Completion.map (star : A → A)
      ((a : C) * (b : C)) =
        UniformSpace.Completion.map (star : A → A) (b : C) *
          UniformSpace.Completion.map (star : A → A) (a : C)
    rw [← nonUnitalCompletion_coe_mul A,
      UniformSpace.Completion.map_coe hUC,
      UniformSpace.Completion.map_coe hUC,
      UniformSpace.Completion.map_coe hUC, star_mul]
    exact nonUnitalCompletion_coe_mul A (star b) (star a)
  exact
    { star := s
      star_involutive := hInv
      star_add := hAdd
      star_mul := hMul }

/-- **Completion images commute with star.** Let `A` be a nonunital seminormed ring with a continuous
ring involution. For every `a ∈ A`, the completed involution satisfies `(ι(a))* = ι(a*)` for the
canonical map `ι` into the completion; injectivity of `ι` is not assumed. -/
@[simp]
theorem nonUnitalCompletionStarRing_star_coe
    (A : Type uA) [NonUnitalSeminormedRing A]
    [StarRing A] [ContinuousStar A] (a : A) :
    letI : NonUnitalNormedRing (UniformSpace.Completion A) :=
      nonUnitalCompletionNormedRing A;
    letI : StarRing (UniformSpace.Completion A) :=
      nonUnitalCompletionStarRing A;
    star (a : UniformSpace.Completion A) =
      ((star a : A) : UniformSpace.Completion A) := by
  let : NonUnitalNormedRing (UniformSpace.Completion A) :=
    nonUnitalCompletionNormedRing A
  let : StarRing (UniformSpace.Completion A) :=
    nonUnitalCompletionStarRing A
  change UniformSpace.Completion.map (star : A → A)
    (a : UniformSpace.Completion A) = ((star a : A) : UniformSpace.Completion A)
  let fStar : A →+ A := (starAddEquiv : A ≃+ A).toAddMonoidHom
  have hUC : UniformContinuous (star : A → A) :=
    uniformContinuous_addMonoidHom_of_continuous (f := fStar)
      (show Continuous fStar from continuous_star)
  exact UniformSpace.Completion.map_coe hUC a

/-- **Continuity of the completed involution.** Let `A` be a nonunital seminormed ring with a continuous
ring involution. The extended involution is continuous for the uniform-completion topology. -/
theorem nonUnitalCompletionStarRing_continuousStar
    (A : Type uA) [NonUnitalSeminormedRing A]
    [StarRing A] [ContinuousStar A] :
    letI : NonUnitalNormedRing (UniformSpace.Completion A) :=
      nonUnitalCompletionNormedRing A;
    letI : StarRing (UniformSpace.Completion A) :=
      nonUnitalCompletionStarRing A;
    ContinuousStar (UniformSpace.Completion A) := by
  let : NonUnitalNormedRing (UniformSpace.Completion A) :=
    nonUnitalCompletionNormedRing A
  let : StarRing (UniformSpace.Completion A) :=
    nonUnitalCompletionStarRing A
  refine { continuous_star := ?_ }
  change Continuous (UniformSpace.Completion.map (star : A → A))
  exact UniformSpace.Completion.continuous_map

end UniformSpace.Completion

end

end

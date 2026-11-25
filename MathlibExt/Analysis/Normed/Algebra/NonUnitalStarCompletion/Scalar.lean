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

/-!
# Scalar compatibility of the canonical completed involution

The existing completion action is retained. Its fixed-scalar maps are
continuous, so the source star-module law extends by closed equality on
the dense coefficient images under the canonical completed star.

Only a star-equipped scalar type and uniformly continuous source action
are required. No scalar monoid, semiring, topology or norm, source
completeness or separatedness, or new action structure is assumed.
-/

@[expose] public section

noncomputable section

namespace UniformSpace.Completion

universe uR uA

/-- **Scalar compatibility of the completed involution.** Let `A` be a nonunital seminormed ring with
continuous ring involution, and let a type `R` with a star operation act on `A`. If every
fixed-scalar map is uniformly continuous and `(r • a)* = r* • a*`, the extended action and
involution on the uniform completion satisfy the same identity. -/
theorem nonUnitalCompletionStarRing_starModule
    {R : Type uR} (A : Type uA)
    [NonUnitalSeminormedRing A] [StarRing A] [ContinuousStar A]
    [Star R] [SMul R A] [UniformContinuousConstSMul R A]
    [StarModule R A] :
    letI : NonUnitalNormedRing (UniformSpace.Completion A) :=
      nonUnitalCompletionNormedRing A;
    letI : StarRing (UniformSpace.Completion A) :=
      nonUnitalCompletionStarRing A;
    StarModule R (UniformSpace.Completion A) := by
  let C := UniformSpace.Completion A
  let rC : NonUnitalNormedRing C := nonUnitalCompletionNormedRing A
  let : NonUnitalNormedRing C := rC
  let rS : StarRing C := nonUnitalCompletionStarRing A
  let : StarRing C := rS
  let : ContinuousStar C := nonUnitalCompletionStarRing_continuousStar A
  refine { star_smul := ?_ }
  intro c x
  have hLeft : Continuous (fun x : C => star (c • x)) :=
    continuous_star.comp (continuous_const_smul c)
  have hRight : Continuous (fun x : C => star c • star x) :=
    (continuous_const_smul (star c)).comp continuous_star
  refine UniformSpace.Completion.induction_on
    (α := A) (p := fun x : C => star (c • x) = star c • star x)
    x (isClosed_eq hLeft hRight) ?_
  intro a
  calc
    star (c • (a : C)) = star ((c • a : A) : C) :=
      congrArg (star : C → C) (UniformSpace.Completion.coe_smul c a).symm
    _ = ((star (c • a) : A) : C) :=
      nonUnitalCompletionStarRing_star_coe A (c • a)
    _ = ((star c • star a : A) : C) :=
      congrArg ((↑) : A → C) (star_smul c a)
    _ = star c • ((star a : A) : C) :=
      UniformSpace.Completion.coe_smul (star c) (star a)
    _ = star c • star (a : C) :=
      congrArg (fun z : C => star c • z)
        (nonUnitalCompletionStarRing_star_coe A a).symm

end UniformSpace.Completion

end

end

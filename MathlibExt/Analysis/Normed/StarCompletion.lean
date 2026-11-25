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

public import MathlibExt.Analysis.Normed.Algebra.NonUnitalStarCompletion.Scalar
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Topology.Algebra.Star

/-!
# The original involution on the ordinary ring completion

The existing continuous-star nonunital completion hierarchy supplies the
actual involution, ring laws and scalar law. For a unital source its completed
nonunital normed-ring dictionary is definitionally the stock completion parent.
The primary factories therefore reuse that hierarchy directly and require only
continuous source star. The stock completed ring, norm and scalar action remain
unchanged, with no new global completion instance.

The older normed-star factories retain their original signatures and values as
compatibility wrappers. Only the norm-isometry result needs NormedStarGroup;
it uses the stock isometric completion map.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UniformSpace.Completion

noncomputable section

universe u v

/-- Let `A` be a seminormed ring. The completion uses its additive uniformity and the canonical
extended multiplication.

The existing nonunital completion factory is exactly the unital completion's nonunital parent. -/
theorem nonUnitalCompletionNormedRing_eq (A : Type u) [SeminormedRing A] :
    nonUnitalCompletionNormedRing A =
      (inferInstance : NonUnitalNormedRing (Completion A)) :=
  rfl

section Continuous

variable (A : Type u) [SeminormedRing A] [StarRing A] [ContinuousStar A]

/-- Let `A` be a seminormed ring with an involution satisfying the star-ring laws and continuous for
its norm topology. Its completion carries the extended involution.

The primary completed star ring reuses the existing weak hierarchy over the ring. -/
@[instance_reducible]
def completionStarRing : StarRing (Completion A) :=
  nonUnitalCompletionStarRing A

/-- Let `A` be a seminormed ring with an involution satisfying the star-ring laws and continuous for
its norm topology. Its completion carries the extended involution.

Both factories have exactly the same star-ring structure. -/
theorem completionStarRing_eq_nonUnital :
    completionStarRing A = nonUnitalCompletionStarRing A :=
  rfl

/-- Let `A` be a seminormed ring with an involution satisfying the star-ring laws and continuous for
its norm topology. Its completion carries the extended involution.

The shared involution agrees with source star on every dense coefficient. -/
theorem completionStarRing_star_coe (a : A) :
    letI : StarRing (Completion A) := completionStarRing A
    star (a : Completion A) = ((star a : A) : Completion A) := by
  exact nonUnitalCompletionStarRing_star_coe A a

/-- Let `A` be a seminormed ring with an involution satisfying the star-ring laws and continuous for
its norm topology. Its completion carries the extended involution.

The shared completed involution is continuous for the completion topology. -/
theorem completionStarRing_continuousStar :
    letI : StarRing (Completion A) := completionStarRing A
    ContinuousStar (Completion A) := by
  exact nonUnitalCompletionStarRing_continuousStar A

/-- Let `A` be a seminormed ring with an involution satisfying the star-ring laws and continuous for
its norm topology. Its completion carries the extended involution. A scalar type `R` acts with
uniformly continuous constant scalar maps, an involution, and compatibility of scalar action
with the involutions.

The primary scalar law reuses the completion action and only uniform source scalar maps. -/
theorem completionStarModule {R : Type v}
    [Star R] [SMul R A] [UniformContinuousConstSMul R A] [StarModule R A] :
    letI : StarRing (Completion A) := completionStarRing A
    StarModule R (Completion A) := by
  exact nonUnitalCompletionStarRing_starModule A

end Continuous

section Compatibility

variable (A : Type u) [NormedRing A] [StarRing A] [NormedStarGroup A]

/-- Let `A` be a normed ring with a star-ring involution which is isometric. Its completion has the
extended norm and involution.

Compatibility wrapper with the normed-star signature and shared star value. Use
completionStarRing when only continuous source star is available. -/
@[instance_reducible]
def normedStarRing : StarRing (Completion A) :=
  completionStarRing A

/-- Let `A` be a normed ring with a star-ring involution which is isometric. Its completion has the
extended norm and involution.

The named coefficient characteristic for the same shared completion star. -/
theorem normedStarRing_star_coe (a : A) :
    let _ : StarRing (Completion A) := normedStarRing A
    star (a : Completion A) = ((star a : A) : Completion A) := by
  exact completionStarRing_star_coe A a

/-- Let `A` be a normed ring with a star-ring involution which is isometric. Its completion has the
extended norm and involution.

Norm-star isometry alone needs the source normed-star hypothesis, on the completed norm. -/
theorem normedStarGroup :
    let _ : StarRing (Completion A) := normedStarRing A
    NormedStarGroup (Completion A) := by
  let _ : StarRing (Completion A) := normedStarRing A
  have hIso : Isometry (star : Completion A → Completion A) := by
    change Isometry (Completion.map (star : A → A))
    exact (star_isometry : Isometry (star : A → A)).completion_map
  refine { norm_star_le := ?_ }
  intro x
  have hnorm : ‖star x‖ = ‖x‖ := by
    simpa only [star_zero, dist_eq_norm, sub_zero] using hIso.dist_eq x 0
  exact hnorm.le

variable [NormedAlgebra ℂ A] [StarModule ℂ A]

/-- Let `A` be a normed ring with a star-ring involution which is isometric. Its completion has the
extended norm and involution. For scalar compatibility, `A` is also a normed complex algebra
with a compatible scalar involution.

Compatibility wrapper with the complex normed-star signature and shared scalar law. Use
completionStarModule for the continuous-star and general-scalar interface. -/
theorem normedStarModule :
    let _ : StarRing (Completion A) := normedStarRing A
    StarModule ℂ (Completion A) := by
  exact completionStarModule A

end Compatibility

end

end UniformSpace.Completion

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

public import MathlibExt.Analysis.Normed.Operator.ArensStar

/-!
# Original Arens maps and involution in the fixed weak-star views

The first Arens extension with its second variable fixed is a continuous
linear map on the original first weak-star bidual. The second extension
with its first variable fixed has the corresponding continuous linear map
on the second weak-star bidual. Their values are the existing extensions.

The original dual involution is a conjugate-linear continuous equivalence
on the weak-star view paired with the same coefficient space. Changing
views preserves its values and the original continuous-dual norm.

These data require only the original bounded bilinear map and isometric
additive involution. No equality of the Arens products, C-star identity,
unit, selected predual or representation model is used.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped StrongDual

universe u v w z

attribute [local instance]
  ContinuousLinearMap.arensDualSeminormed
  ContinuousLinearMap.arensDualNormedSpace
  ContinuousLinearMap.arensDualTargetSeminormed
  ContinuousLinearMap.arensDualTargetNormedSpace
  ContinuousLinearMap.arensDualTargetTopologicalAddGroup
  ContinuousLinearMap.arensMapSeminormed
  ContinuousLinearMap.arensMapNormedSpace
  ContinuousLinearMap.arensMapTopologicalAddGroup
  ContinuousLinearMap.arensBidualSeminormed
  ContinuousLinearMap.arensBidualNormedSpace
  ContinuousLinearMap.arensBidualMapSeminormed
  ContinuousLinearMap.arensBidualMapNormedSpace
  ContinuousLinearMap.arensBidualMapTopologicalAddGroup
  ContinuousLinearMap.arensAlgebraDualNormedGroup

namespace ContinuousLinearMap

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} {F : Type w} {G : Type z}
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The actual first Arens extension in its continuous first weak-star variable. -/
def arensFirstWeakLeft (m : E →L[𝕜] F →L[𝕜] G)
    (q : StrongDual 𝕜 (StrongDual 𝕜 F)) :
    WeakDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] WeakDual 𝕜 (StrongDual 𝕜 G) where
  toLinearMap :=
    (StrongDual.toWeakDual (𝕜 := 𝕜) (E := StrongDual 𝕜 E)).arrowCongr
      (StrongDual.toWeakDual (𝕜 := 𝕜) (E := StrongDual 𝕜 G))
      (m.arensFirst.flip q).toLinearMap
  cont := continuous_arensFirst_weakDual_left m q

/-- Changing views leaves the actual first Arens value unchanged. -/
@[simp] theorem arensFirstWeakLeft_apply (m : E →L[𝕜] F →L[𝕜] G)
    (q : StrongDual 𝕜 (StrongDual 𝕜 F)) (p : WeakDual 𝕜 (StrongDual 𝕜 E)) :
    m.arensFirstWeakLeft q p = StrongDual.toWeakDual (m.arensFirst p.toStrongDual q) := rfl

/-- The first weak-star map evaluates at the original iterated dual action. -/
@[simp] theorem arensFirstWeakLeft_apply_apply (m : E →L[𝕜] F →L[𝕜] G)
    (q : StrongDual 𝕜 (StrongDual 𝕜 F)) (p : WeakDual 𝕜 (StrongDual 𝕜 E))
    (phi : StrongDual 𝕜 G) :
    m.arensFirstWeakLeft q p phi = p (m.dualBilinear.dualBilinear q phi) := rfl

/-- The actual second Arens extension in its continuous second weak-star variable. -/
def arensSecondWeakRight (m : E →L[𝕜] F →L[𝕜] G)
    (p : StrongDual 𝕜 (StrongDual 𝕜 E)) :
    WeakDual 𝕜 (StrongDual 𝕜 F) →L[𝕜] WeakDual 𝕜 (StrongDual 𝕜 G) where
  toLinearMap :=
    (StrongDual.toWeakDual (𝕜 := 𝕜) (E := StrongDual 𝕜 F)).arrowCongr
      (StrongDual.toWeakDual (𝕜 := 𝕜) (E := StrongDual 𝕜 G))
      (m.arensSecond p).toLinearMap
  cont := continuous_arensSecond_weakDual_right m p

/-- Changing views leaves the actual second Arens value unchanged. -/
@[simp] theorem arensSecondWeakRight_apply (m : E →L[𝕜] F →L[𝕜] G)
    (p : StrongDual 𝕜 (StrongDual 𝕜 E)) (q : WeakDual 𝕜 (StrongDual 𝕜 F)) :
    m.arensSecondWeakRight p q = StrongDual.toWeakDual (m.arensSecond p q.toStrongDual) := rfl

/-- The second weak-star map retains the original second outer evaluation. -/
@[simp] theorem arensSecondWeakRight_apply_apply (m : E →L[𝕜] F →L[𝕜] G)
    (p : StrongDual 𝕜 (StrongDual 𝕜 E)) (q : WeakDual 𝕜 (StrongDual 𝕜 F))
    (phi : StrongDual 𝕜 G) :
    m.arensSecondWeakRight p q phi = q (m.flip.dualBilinear.dualBilinear p phi) := rfl

end ContinuousLinearMap

namespace WeakDual

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [StarRing 𝕜] [NormedStarGroup 𝕜]
variable {A : Type v} [SeminormedAddCommGroup A] [StarAddMonoid A]
variable [NormedSpace 𝕜 A] [StarModule 𝕜 A] [NormedStarGroup A]

/-- The original conjugate-linear dual involution as a weak-star continuous equivalence. -/
def intrinsicStarContinuousLinearEquiv : WeakDual 𝕜 A ≃L⋆[𝕜] WeakDual 𝕜 A where
  toLinearEquiv :=
    ((toStrongDual (𝕜 := 𝕜) (E := A)).trans
      (StrongDual.intrinsicStarIsometry (𝕜 := 𝕜) (A := A)).toLinearEquiv).trans
      (StrongDual.toWeakDual (𝕜 := 𝕜) (E := A))
  continuous_toFun := by
    apply WeakDual.continuous_of_continuous_eval
    intro a
    change Continuous (fun phi : WeakDual 𝕜 A => star (phi (star a)))
    exact (WeakDual.eval_continuous (star a)).star
  continuous_invFun := by
    apply WeakDual.continuous_of_continuous_eval
    intro a
    change Continuous (fun phi : WeakDual 𝕜 A => star (phi (star a)))
    exact (WeakDual.eval_continuous (star a)).star

/-- Weak-star evaluation uses the original coefficient involution and scalar conjugation. -/
@[simp] theorem intrinsicStarContinuousLinearEquiv_apply (phi : WeakDual 𝕜 A) (a : A) :
    intrinsicStarContinuousLinearEquiv phi a = star (phi (star a)) := rfl

/-- The original normed view retains exactly the pre-existing dual involution. -/
@[simp] theorem intrinsicStarContinuousLinearEquiv_toStrongDual (phi : WeakDual 𝕜 A) :
    (intrinsicStarContinuousLinearEquiv phi).toStrongDual =
      StrongDual.intrinsicStarIsometry phi.toStrongDual := rfl

/-- The same original continuous-dual norm is preserved after changing views. -/
theorem intrinsicStarContinuousLinearEquiv_norm (phi : WeakDual 𝕜 A) :
    ‖(intrinsicStarContinuousLinearEquiv phi).toStrongDual‖ = ‖phi.toStrongDual‖ :=
  (StrongDual.intrinsicStarIsometry (𝕜 := 𝕜) (A := A)).norm_map phi.toStrongDual

end WeakDual

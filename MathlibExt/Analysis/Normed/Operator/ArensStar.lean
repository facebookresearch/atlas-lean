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

public import MathlibExt.Analysis.Normed.Module.StrongDualStar
public import MathlibExt.Analysis.Normed.Operator.ArensAlgebra

/-!
# Involution interchanges the two original Arens products

The first product reverses into the second product under the original
dual involution. This uses only the original coefficient multiplication's
star-reversal law. No equality of the Arens products and no StarRing
structure on the first-Arens bidual is assumed or installed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped StrongDual

universe u v

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

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [StarRing 𝕜] [NormedStarGroup 𝕜]
variable {A : Type v} [SeminormedAddCommGroup A] [StarAddMonoid A]
variable [NormedSpace 𝕜 A] [StarModule 𝕜 A] [NormedStarGroup A]

/-- The original dual involution reverses the first Arens product into the second. -/
theorem arensFirst_star (m : A →L[𝕜] A →L[𝕜] A)
    (h : ∀ a b, star (m a b) = m (star b) (star a))
    (p q : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    star (m.arensFirst p q) = m.arensSecond (star q) (star p) := by
  apply ContinuousLinearMap.ext
  intro phi
  change star (p (m.dualBilinear.dualBilinear q (star phi))) =
    star (p (star (m.flip.dualBilinear.dualBilinear (star q) phi)))
  apply congrArg (star : 𝕜 → 𝕜)
  apply congrArg (fun f : StrongDual 𝕜 A => p f)
  apply ContinuousLinearMap.ext
  intro a
  change q (m.dualBilinear (star phi) a) =
    star (star q (m.flip.dualBilinear phi (star a)))
  rw [StrongDual.star_apply, star_star]
  apply congrArg (fun f : StrongDual 𝕜 A => q f)
  apply ContinuousLinearMap.ext
  intro b
  change star (phi (star (m a b))) = star (phi (m (star b) (star a)))
  rw [h a b]

/-- The same involution reverses the second Arens product into the first. -/
theorem arensSecond_star (m : A →L[𝕜] A →L[𝕜] A)
    (h : ∀ a b, star (m a b) = m (star b) (star a))
    (p q : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    star (m.arensSecond p q) = m.arensFirst (star q) (star p) := by
  have h' := congrArg star (arensFirst_star m h (star q) (star p))
  simpa only [star_star] using h'.symm

end ContinuousLinearMap

namespace NormedSpace

variable (𝕜 : Type u) [NontriviallyNormedField 𝕜] [StarRing 𝕜] [NormedStarGroup 𝕜]
variable (A : Type v) [NonUnitalSeminormedRing A] [StarRing A] [NormedStarGroup A]
variable [NormedSpace 𝕜 A] [StarModule 𝕜 A]
variable [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- Original nonunital star multiplication gives the exact first-to-second reversal. -/
theorem firstArens_star_mul (p q : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    star ((ContinuousLinearMap.mul 𝕜 A).arensFirst p q) =
      (ContinuousLinearMap.mul 𝕜 A).arensSecond (star q) (star p) :=
  (ContinuousLinearMap.mul 𝕜 A).arensFirst_star (fun a b => star_mul a b) p q

/-- Original nonunital star multiplication gives the exact second-to-first reversal. -/
theorem secondArens_star_mul (p q : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    star ((ContinuousLinearMap.mul 𝕜 A).arensSecond p q) =
      (ContinuousLinearMap.mul 𝕜 A).arensFirst (star q) (star p) :=
  (ContinuousLinearMap.mul 𝕜 A).arensSecond_star (fun a b => star_mul a b) p q

end NormedSpace

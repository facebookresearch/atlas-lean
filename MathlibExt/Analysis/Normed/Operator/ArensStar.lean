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
# Involution reverses the two Arens extensions

Let `𝕜` be a nontrivially normed star field and `A` a seminormed `𝕜`-space with compatible
isometric additive involution. If a bounded bilinear map `m` obeys `m(a,b)*=m(b*,a*)`, its
bidual extensions satisfy `m₁(p,q)*=m₂(q*,p*)` and `m₂(p,q)*=m₁(q*,p*)`.

In a nonunital seminormed star ring these are the involution laws for the first and second Arens
products. Equality of those products is not assumed. Coefficient spaces may be incomplete or
zero.
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

/-- **Star reversal of the first Arens extension.** Let `𝕜` be a nontrivially normed field
with an isometric star-ring involution. Let `A` be a seminormed `𝕜`-space with an
isometric additive involution satisfying `(c • a)*=c* • a*`. The bidual involution is
`p*(φ)=star(p(φ*))`, where `φ*(a)=star(φ(a*))`. for a bounded bilinear `m : A×A → A`
satisfying `m(a,b)*=m(b*,a*)`, `star(m.arensFirst p q)=m.arensSecond (star q) (star p)`
for `p,q ∈ A**`. -/
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

/-- **Star reversal of the second Arens extension.** Let `𝕜` be a nontrivially normed field
with an isometric star-ring involution. Let `A` be a seminormed `𝕜`-space with an
isometric additive involution satisfying `(c • a)*=c* • a*`. The bidual involution is
`p*(φ)=star(p(φ*))`, where `φ*(a)=star(φ(a*))`. for a bounded bilinear `m : A×A → A`
satisfying `m(a,b)*=m(b*,a*)`, `star(m.arensSecond p q)=m.arensFirst (star q) (star p)`
for `p,q ∈ A**`. -/
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

/-- **Involution changes the first Arens product to the second.** Let `𝕜` be a nontrivially
normed field with an isometric star-ring involution. Let `A` be a seminormed `𝕜`-space
with an isometric additive involution satisfying `(c • a)*=c* • a*`. The bidual involution
is `p*(φ)=star(p(φ*))`, where `φ*(a)=star(φ(a*))`. Assume `A` is a nonunital seminormed
star ring and its scalar action is compatible with both multiplication factors. for `p,q ∈
A**`, `(p □ q)*=q* ◇ p*`, where `□,◇` are the first and second Arens extensions of
multiplication. -/
theorem firstArens_star_mul (p q : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    star ((ContinuousLinearMap.mul 𝕜 A).arensFirst p q) =
      (ContinuousLinearMap.mul 𝕜 A).arensSecond (star q) (star p) :=
  (ContinuousLinearMap.mul 𝕜 A).arensFirst_star (fun a b => star_mul a b) p q

/-- **Involution changes the second Arens product to the first.** Let `𝕜` be a nontrivially
normed field with an isometric star-ring involution. Let `A` be a seminormed `𝕜`-space
with an isometric additive involution satisfying `(c • a)*=c* • a*`. The bidual involution
is `p*(φ)=star(p(φ*))`, where `φ*(a)=star(φ(a*))`. Assume `A` is a nonunital seminormed
star ring and its scalar action is compatible with both multiplication factors. for `p,q ∈
A**`, `(p ◇ q)*=q* □ p*`, where `□,◇` are the first and second Arens products. -/
theorem secondArens_star_mul (p q : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    star ((ContinuousLinearMap.mul 𝕜 A).arensSecond p q) =
      (ContinuousLinearMap.mul 𝕜 A).arensFirst (star q) (star p) :=
  (ContinuousLinearMap.mul 𝕜 A).arensSecond_star (fun a b => star_mul a b) p q

end NormedSpace

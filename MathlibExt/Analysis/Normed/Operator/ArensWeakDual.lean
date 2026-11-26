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
# Weak-star Arens maps and the continuous dual involution

For a bounded bilinear map `m : E×F → G` on seminormed spaces over a nontrivially normed field,
fixing `q ∈ F**` gives the weak-star continuous linear map `p ↦ m₁(p,q)` from `E**` to `G**`.
Fixing `p ∈ E**` gives `q ↦ m₂(p,q)` from `F**` to `G**`.

For a coefficient space `A` with compatible isometric involution over a normed star field,
`φ*(a)=star(φ(a*))` is a conjugate-linear weak-star continuous equivalence of `A*`. It preserves
the operator norm. Completeness and equality of the two Arens extensions are not required.
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

/-- **Weak-star continuous first Arens map.** Let `𝕜` be a nontrivially normed field. Let
`E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`, `E**` for the
continuous dual and bidual, with their operator norms. Let `m : E →L[𝕜] F →L[𝕜] G` be a
bounded bilinear map. for fixed `q ∈ F**`, `arensFirstWeakLeft m q` is the continuous
linear map `p ↦ m.arensFirst p q` from `E**` with `σ(E**,E*)` to `G**` with `σ(G**,G*)`. -/
def arensFirstWeakLeft (m : E →L[𝕜] F →L[𝕜] G)
    (q : StrongDual 𝕜 (StrongDual 𝕜 F)) :
    WeakDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] WeakDual 𝕜 (StrongDual 𝕜 G) where
  toLinearMap :=
    (StrongDual.toWeakDual (𝕜 := 𝕜) (E := StrongDual 𝕜 E)).arrowCongr
      (StrongDual.toWeakDual (𝕜 := 𝕜) (E := StrongDual 𝕜 G))
      (m.arensFirst.flip q).toLinearMap
  cont := continuous_arensFirst_weakDual_left m q

/-- **First Arens value in weak-star biduals.** Let `𝕜` be a nontrivially normed field. Let
`E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`, `E**` for the
continuous dual and bidual, with their operator norms. Let `m : E →L[𝕜] F →L[𝕜] G` be a
bounded bilinear map. for `q ∈ F**` and `p` in the weak-star view of `E**`,
`arensFirstWeakLeft m q p` is the weak-star view of `m.arensFirst p q`; evaluations are
unchanged. -/
@[simp] theorem arensFirstWeakLeft_apply (m : E →L[𝕜] F →L[𝕜] G)
    (q : StrongDual 𝕜 (StrongDual 𝕜 F)) (p : WeakDual 𝕜 (StrongDual 𝕜 E)) :
    m.arensFirstWeakLeft q p = StrongDual.toWeakDual (m.arensFirst p.toStrongDual q) := rfl

/-- **Nested evaluation of the weak-star first Arens map.** Let `𝕜` be a nontrivially normed
field. Let `E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`,
`E**` for the continuous dual and bidual, with their operator norms. Let `m : E →L[𝕜] F
→L[𝕜] G` be a bounded bilinear map. for `p ∈ E**`, `q ∈ F**` and `φ ∈ G*`,
`(arensFirstWeakLeft m q p)(φ)=p(x ↦ q(y ↦ φ(m(x,y))))`. -/
@[simp] theorem arensFirstWeakLeft_apply_apply (m : E →L[𝕜] F →L[𝕜] G)
    (q : StrongDual 𝕜 (StrongDual 𝕜 F)) (p : WeakDual 𝕜 (StrongDual 𝕜 E))
    (phi : StrongDual 𝕜 G) :
    m.arensFirstWeakLeft q p phi = p (m.dualBilinear.dualBilinear q phi) := rfl

/-- **Weak-star continuous second Arens map.** Let `𝕜` be a nontrivially normed field. Let
`E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`, `E**` for the
continuous dual and bidual, with their operator norms. Let `m : E →L[𝕜] F →L[𝕜] G` be a
bounded bilinear map. for fixed `p ∈ E**`, `arensSecondWeakRight m p` is the continuous
linear map `q ↦ m.arensSecond p q` from `F**` with `σ(F**,F*)` to `G**` with `σ(G**,G*)`. -/
def arensSecondWeakRight (m : E →L[𝕜] F →L[𝕜] G)
    (p : StrongDual 𝕜 (StrongDual 𝕜 E)) :
    WeakDual 𝕜 (StrongDual 𝕜 F) →L[𝕜] WeakDual 𝕜 (StrongDual 𝕜 G) where
  toLinearMap :=
    (StrongDual.toWeakDual (𝕜 := 𝕜) (E := StrongDual 𝕜 F)).arrowCongr
      (StrongDual.toWeakDual (𝕜 := 𝕜) (E := StrongDual 𝕜 G))
      (m.arensSecond p).toLinearMap
  cont := continuous_arensSecond_weakDual_right m p

/-- **Second Arens value in weak-star biduals.** Let `𝕜` be a nontrivially normed field. Let
`E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`, `E**` for the
continuous dual and bidual, with their operator norms. Let `m : E →L[𝕜] F →L[𝕜] G` be a
bounded bilinear map. for `p ∈ E**` and `q` in the weak-star view of `F**`,
`arensSecondWeakRight m p q` is the weak-star view of `m.arensSecond p q`. -/
@[simp] theorem arensSecondWeakRight_apply (m : E →L[𝕜] F →L[𝕜] G)
    (p : StrongDual 𝕜 (StrongDual 𝕜 E)) (q : WeakDual 𝕜 (StrongDual 𝕜 F)) :
    m.arensSecondWeakRight p q = StrongDual.toWeakDual (m.arensSecond p q.toStrongDual) := rfl

/-- **Nested evaluation of the weak-star second Arens map.** Let `𝕜` be a nontrivially normed
field. Let `E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`,
`E**` for the continuous dual and bidual, with their operator norms. Let `m : E →L[𝕜] F
→L[𝕜] G` be a bounded bilinear map. for `p ∈ E**`, `q ∈ F**` and `φ ∈ G*`,
`(arensSecondWeakRight m p q)(φ)=q(y ↦ p(x ↦ φ(m(x,y))))`. -/
@[simp] theorem arensSecondWeakRight_apply_apply (m : E →L[𝕜] F →L[𝕜] G)
    (p : StrongDual 𝕜 (StrongDual 𝕜 E)) (q : WeakDual 𝕜 (StrongDual 𝕜 F))
    (phi : StrongDual 𝕜 G) :
    m.arensSecondWeakRight p q phi = q (m.flip.dualBilinear.dualBilinear p phi) := rfl

end ContinuousLinearMap

namespace WeakDual

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [StarRing 𝕜] [NormedStarGroup 𝕜]
variable {A : Type v} [SeminormedAddCommGroup A] [StarAddMonoid A]
variable [NormedSpace 𝕜 A] [StarModule 𝕜 A] [NormedStarGroup A]

/-- **Weak-star continuous conjugate-linear dual involution.** Let `𝕜` be a nontrivially
normed field with an isometric star-ring involution. Let `A` be a seminormed `𝕜`-space
with an isometric additive involution satisfying `(c • a)*=c* • a*`. The bidual involution
is `p*(φ)=star(p(φ*))`, where `φ*(a)=star(φ(a*))`. on `A*` with `σ(A*,A)`,
`intrinsicStarContinuousLinearEquiv` is the conjugate-linear continuous equivalence `φ ↦
φ*`, where `φ*(a)=star(φ(a*))`. -/
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

/-- **Evaluation of the weak-star dual involution.** Let `𝕜` be a nontrivially normed field
with an isometric star-ring involution. Let `A` be a seminormed `𝕜`-space with an
isometric additive involution satisfying `(c • a)*=c* • a*`. The bidual involution is
`p*(φ)=star(p(φ*))`, where `φ*(a)=star(φ(a*))`. for `φ ∈ A*` and `a ∈ A`,
`(intrinsicStarContinuousLinearEquiv φ)(a)=star(φ(star a))`. -/
@[simp] theorem intrinsicStarContinuousLinearEquiv_apply (phi : WeakDual 𝕜 A) (a : A) :
    intrinsicStarContinuousLinearEquiv phi a = star (phi (star a)) := rfl

/-- **Dual involution in the operator-norm view.** Let `𝕜` be a nontrivially normed field with
an isometric star-ring involution. Let `A` be a seminormed `𝕜`-space with an isometric
additive involution satisfying `(c • a)*=c* • a*`. The bidual involution is
`p*(φ)=star(p(φ*))`, where `φ*(a)=star(φ(a*))`. viewing
`intrinsicStarContinuousLinearEquiv φ` as a normed continuous functional gives
`StrongDual.intrinsicStarIsometry φ`, with evaluation `a ↦ star(φ(star a))`. -/
@[simp] theorem intrinsicStarContinuousLinearEquiv_toStrongDual (phi : WeakDual 𝕜 A) :
    (intrinsicStarContinuousLinearEquiv phi).toStrongDual =
      StrongDual.intrinsicStarIsometry phi.toStrongDual := rfl

/-- **Operator norm preserved by the weak-star dual involution.** Let `𝕜` be a nontrivially
normed field with an isometric star-ring involution. Let `A` be a seminormed `𝕜`-space
with an isometric additive involution satisfying `(c • a)*=c* • a*`. The bidual involution
is `p*(φ)=star(p(φ*))`, where `φ*(a)=star(φ(a*))`. for `φ ∈ A*`,
`‖(intrinsicStarContinuousLinearEquiv φ).toStrongDual‖=‖φ.toStrongDual‖`, using the
continuous-dual operator norm. -/
theorem intrinsicStarContinuousLinearEquiv_norm (phi : WeakDual 𝕜 A) :
    ‖(intrinsicStarContinuousLinearEquiv phi).toStrongDual‖ = ‖phi.toStrongDual‖ :=
  (StrongDual.intrinsicStarIsometry (𝕜 := 𝕜) (A := A)).norm_map phi.toStrongDual

end WeakDual

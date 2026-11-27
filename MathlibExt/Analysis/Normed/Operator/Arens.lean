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

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# Dual transposes and the two Arens extensions

Let `𝕜` be a nontrivially normed field and `E,F,G` seminormed `𝕜`-spaces in independent
universes. For a bounded bilinear map `m : E × F → G`, its dual transpose is
`m*(φ,x)(y)=φ(m(x,y))`.

For `p ∈ E**`, `q ∈ F**` and `φ ∈ G*`, the Arens extensions satisfy `m₁(p,q)(φ)=p(x ↦ q(y ↦
φ(m(x,y))))` and `m₂(p,q)(φ)=q(y ↦ p(x ↦ φ(m(x,y))))`. Both are bounded bilinear maps into
`G**`, with norm at most `‖m‖`, and both agree with `m` on the evaluation maps into the biduals.

For fixed `q`, `m₁(·,q)` is weak-star continuous; for fixed `p`, `m₂(p,·)` is weak-star
continuous. Neither completeness nor nonzero coefficient spaces is required. Equality of the two
extensions is a separate regularity property.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w z

namespace ContinuousLinearMap

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} {F : Type w} {G : Type z}
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/- The literal local declarations preserve the exact imported stock
instance setup at every iterated transpose level. Their variables are
polymorphic, so the same rules cover later strong-dual and dual-target levels. -/

/-- **Operator seminorm on a continuous dual.** Let `𝕜` be a nontrivially normed field. Let
`E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`, `E**` for the
continuous dual and bidual, with their operator norms. the continuous dual `G*` has the
operator seminorm characterized by the bounds `‖φ(g)‖≤C‖g‖`. -/
local instance arensDualSeminormed : SeminormedAddCommGroup (StrongDual 𝕜 G) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

/-- **Normed scalar action on the continuous dual.** Let `𝕜` be a nontrivially normed field.
Let `E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`, `E**` for
the continuous dual and bidual, with their operator norms. the scalar action on `G*` is
`(c • φ)(g)=c*φ(g)` and satisfies `‖c • φ‖=‖c‖*‖φ‖`. -/
local instance arensDualNormedSpace : NormedSpace 𝕜 (StrongDual 𝕜 G) :=
  ContinuousLinearMap.toNormedSpace

/-- **Operator seminorm on dual-valued maps.** Let `𝕜` be a nontrivially normed field. Let
`E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`, `E**` for the
continuous dual and bidual, with their operator norms. bounded maps `T : E →L[𝕜] F*` have
the operator seminorm for the inequality `‖T(x)‖≤‖T‖‖x‖`, using the dual norm on `F*`. -/
local instance arensDualTargetSeminormed : SeminormedAddCommGroup (E →L[𝕜] StrongDual 𝕜 F) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

/-- **Scalar action on dual-valued operators.** Let `𝕜` be a nontrivially normed field. Let
`E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`, `E**` for the
continuous dual and bidual, with their operator norms. bounded maps `T : E →L[𝕜] F*` form
a normed `𝕜`-space with `(c • T)(x)=c • T(x)`. -/
local instance arensDualTargetNormedSpace : NormedSpace 𝕜 (E →L[𝕜] StrongDual 𝕜 F) :=
  ContinuousLinearMap.toNormedSpace

/-- **Continuous addition of dual-valued operators.** Let `𝕜` be a nontrivially normed field.
Let `E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`, `E**` for
the continuous dual and bidual, with their operator norms. addition and negation on `E
→L[𝕜] F*` are continuous in the operator-norm topology. -/
local instance arensDualTargetTopologicalAddGroup : IsTopologicalAddGroup (E →L[𝕜] StrongDual 𝕜 F) :=
  ContinuousLinearMap.isTopologicalAddGroup

/-- **Operator seminorm of bounded coefficient maps.** Let `𝕜` be a nontrivially normed field.
Let `E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`, `E**` for
the continuous dual and bidual, with their operator norms. `F →L[𝕜] G` has the operator
seminorm for `‖T(y)‖≤‖T‖‖y‖`. -/
local instance arensMapSeminormed : SeminormedAddCommGroup (F →L[𝕜] G) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

/-- **Normed scalar action on bounded coefficient maps.** Let `𝕜` be a nontrivially normed
field. Let `E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`,
`E**` for the continuous dual and bidual, with their operator norms. `F →L[𝕜] G` is a
normed `𝕜`-space for `(c • T)(y)=c • T(y)`. -/
local instance arensMapNormedSpace : NormedSpace 𝕜 (F →L[𝕜] G) :=
  ContinuousLinearMap.toNormedSpace

/-- **Continuous addition of bounded coefficient maps.** Let `𝕜` be a nontrivially normed
field. Let `E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`,
`E**` for the continuous dual and bidual, with their operator norms. addition and negation
on `F →L[𝕜] G` are continuous for the operator-norm topology. -/
local instance arensMapTopologicalAddGroup : IsTopologicalAddGroup (F →L[𝕜] G) :=
  ContinuousLinearMap.isTopologicalAddGroup

/-- **Iterated operator seminorm on the bidual.** Let `𝕜` be a nontrivially normed field. Let
`E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`, `E**` for the
continuous dual and bidual, with their operator norms. `E**=(E*)*` has the operator
seminorm for `‖p(φ)‖≤‖p‖‖φ‖`, where `φ ∈ E*` has its operator norm. -/
local instance arensBidualSeminormed : SeminormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

/-- **Normed scalar action on the bidual.** Let `𝕜` be a nontrivially normed field. Let
`E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`, `E**` for the
continuous dual and bidual, with their operator norms. the bidual `E**` is a normed
`𝕜`-space with `(c • p)(φ)=c*p(φ)`. -/
local instance arensBidualNormedSpace : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toNormedSpace

/-- **Operator seminorm on maps between biduals.** Let `𝕜` be a nontrivially normed field. Let
`E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`, `E**` for the
continuous dual and bidual, with their operator norms. bounded maps `T : F** →L[𝕜] G**`
have the operator seminorm for the iterated dual norms on source and target. -/
local instance arensBidualMapSeminormed : SeminormedAddCommGroup
    (StrongDual 𝕜 (StrongDual 𝕜 F) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 G)) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

/-- **Normed scalar action on bidual-valued operators.** Let `𝕜` be a nontrivially normed
field. Let `E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`,
`E**` for the continuous dual and bidual, with their operator norms. `F** →L[𝕜] G**` has
scalar action `(c • T)(q)=c • T(q)` and its operator seminorm. -/
local instance arensBidualMapNormedSpace : NormedSpace 𝕜
    (StrongDual 𝕜 (StrongDual 𝕜 F) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 G)) :=
  ContinuousLinearMap.toNormedSpace

/-- **Continuous addition of bidual-valued operators.** Let `𝕜` be a nontrivially normed
field. Let `E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`,
`E**` for the continuous dual and bidual, with their operator norms. addition and negation
on `F** →L[𝕜] G**` are continuous in the iterated operator-norm topology. -/
local instance arensBidualMapTopologicalAddGroup : IsTopologicalAddGroup
    (StrongDual 𝕜 (StrongDual 𝕜 F) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 G)) :=
  ContinuousLinearMap.isTopologicalAddGroup

/-- **Bounded dual transpose of a bilinear map.** Let `𝕜` be a nontrivially normed field. Let
`E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`, `E**` for the
continuous dual and bidual, with their operator norms. Let `m : E →L[𝕜] F →L[𝕜] G` be a
bounded bilinear map. `dualBilinear m : G* →L[𝕜] E →L[𝕜] F*` is given by `(dualBilinear m
φ x)(y)=φ(m(x,y))`. -/
noncomputable def dualBilinear (m : E →L[𝕜] F →L[𝕜] G) :
    StrongDual 𝕜 G →L[𝕜] E →L[𝕜] StrongDual 𝕜 F :=
  ((compL 𝕜 F G 𝕜).flip.comp m).flip

/-- **Evaluation of the dual bilinear transpose.** Let `𝕜` be a nontrivially normed field. Let
`E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`, `E**` for the
continuous dual and bidual, with their operator norms. Let `m : E →L[𝕜] F →L[𝕜] G` be a
bounded bilinear map. for `φ ∈ G*`, `x ∈ E` and `y ∈ F`, `m.dualBilinear φ x y=φ(m x y)`. -/
@[simp] theorem dualBilinear_apply (m : E →L[𝕜] F →L[𝕜] G)
    (phi : StrongDual 𝕜 G) (x : E) (y : F) :
    m.dualBilinear phi x y = phi (m x y) := rfl

/-- **Norm bound for a dual bilinear transpose.** Let `𝕜` be a nontrivially normed field. Let
`E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`, `E**` for the
continuous dual and bidual, with their operator norms. Let `m : E →L[𝕜] F →L[𝕜] G` be a
bounded bilinear map. `‖m.dualBilinear‖≤‖m‖` for the bilinear operator norms and the
continuous dual norm. -/
theorem norm_dualBilinear_le (m : E →L[𝕜] F →L[𝕜] G) :
    ‖m.dualBilinear‖ ≤ ‖m‖ := by
  calc
    ‖m.dualBilinear‖ = ‖(compL 𝕜 F G 𝕜).flip.comp m‖ :=
      opNorm_flip ((compL 𝕜 F G 𝕜).flip.comp m)
    _ ≤ ‖(compL 𝕜 F G 𝕜).flip‖ * ‖m‖ := opNorm_comp_le (compL 𝕜 F G 𝕜).flip m
    _ = ‖compL 𝕜 F G 𝕜‖ * ‖m‖ := by rw [opNorm_flip]
    _ ≤ 1 * ‖m‖ := mul_le_mul_of_nonneg_right (norm_compL_le 𝕜 F G 𝕜) (norm_nonneg m)
    _ = ‖m‖ := one_mul _

/-- **Norm of a transposed coefficient functional.** Let `𝕜` be a nontrivially normed field.
Let `E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`, `E**` for
the continuous dual and bidual, with their operator norms. Let `m : E →L[𝕜] F →L[𝕜] G` be
a bounded bilinear map. for `φ ∈ G*` and `x ∈ E`, `‖m.dualBilinear φ x‖≤‖m‖*‖φ‖*‖x‖`. -/
theorem norm_dualBilinear_apply_le (m : E →L[𝕜] F →L[𝕜] G)
    (phi : StrongDual 𝕜 G) (x : E) :
    ‖m.dualBilinear phi x‖ ≤ ‖m‖ * ‖phi‖ * ‖x‖ := by
  exact (m.dualBilinear.le_opNorm₂ phi x).trans <| by
    gcongr
    exact norm_dualBilinear_le m

/-- **First Arens extension of a bounded bilinear map.** Let `𝕜` be a nontrivially normed
field. Let `E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`,
`E**` for the continuous dual and bidual, with their operator norms. Let `m : E →L[𝕜] F
→L[𝕜] G` be a bounded bilinear map. `m₁=m.arensFirst : E** →L[𝕜] F** →L[𝕜] G**` satisfies
`m₁(p,q)(φ)=p(x ↦ q(y ↦ φ(m(x,y))))`. -/
noncomputable def arensFirst (m : E →L[𝕜] F →L[𝕜] G) :
    StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜]
      StrongDual 𝕜 (StrongDual 𝕜 F) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 G) :=
  m.dualBilinear.dualBilinear.dualBilinear

/-- **Second Arens extension of a bounded bilinear map.** Let `𝕜` be a nontrivially normed
field. Let `E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`,
`E**` for the continuous dual and bidual, with their operator norms. Let `m : E →L[𝕜] F
→L[𝕜] G` be a bounded bilinear map. `m₂=m.arensSecond : E** →L[𝕜] F** →L[𝕜] G**` satisfies
`m₂(p,q)(φ)=q(y ↦ p(x ↦ φ(m(x,y))))`, preserving the order of the inputs to `m`. -/
noncomputable def arensSecond (m : E →L[𝕜] F →L[𝕜] G) :
    StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜]
      StrongDual 𝕜 (StrongDual 𝕜 F) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 G) :=
  m.flip.arensFirst.flip

/-- **Nested coefficient formula for the first Arens extension.** Let `𝕜` be a nontrivially
normed field. Let `E,F,G` be seminormed `𝕜`-spaces in independent universes, and write
`E*`, `E**` for the continuous dual and bidual, with their operator norms. Let `m : E
→L[𝕜] F →L[𝕜] G` be a bounded bilinear map. for `p ∈ E**`, `q ∈ F**` and `φ ∈ G*`,
`m.arensFirst p q φ=p(x ↦ q(y ↦ φ(m(x,y))))`. -/
@[simp] theorem arensFirst_apply (m : E →L[𝕜] F →L[𝕜] G)
    (p : StrongDual 𝕜 (StrongDual 𝕜 E))
    (q : StrongDual 𝕜 (StrongDual 𝕜 F)) (phi : StrongDual 𝕜 G) :
    m.arensFirst p q phi = p (m.dualBilinear.dualBilinear q phi) := rfl

/-- **Nested coefficient formula for the second Arens extension.** Let `𝕜` be a nontrivially
normed field. Let `E,F,G` be seminormed `𝕜`-spaces in independent universes, and write
`E*`, `E**` for the continuous dual and bidual, with their operator norms. Let `m : E
→L[𝕜] F →L[𝕜] G` be a bounded bilinear map. for `p ∈ E**`, `q ∈ F**` and `φ ∈ G*`,
`m.arensSecond p q φ=q(y ↦ p(x ↦ φ(m(x,y))))`. -/
@[simp] theorem arensSecond_apply (m : E →L[𝕜] F →L[𝕜] G)
    (p : StrongDual 𝕜 (StrongDual 𝕜 E))
    (q : StrongDual 𝕜 (StrongDual 𝕜 F)) (phi : StrongDual 𝕜 G) :
    m.arensSecond p q phi = q (m.flip.dualBilinear.dualBilinear p phi) := rfl

/-- **Bilinear norm of the first Arens extension.** Let `𝕜` be a nontrivially normed field.
Let `E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`, `E**` for
the continuous dual and bidual, with their operator norms. Let `m : E →L[𝕜] F →L[𝕜] G` be
a bounded bilinear map. `‖m.arensFirst‖≤‖m‖` in the iterated operator norms. -/
theorem norm_arensFirst_le (m : E →L[𝕜] F →L[𝕜] G) : ‖m.arensFirst‖ ≤ ‖m‖ :=
  (norm_dualBilinear_le m.dualBilinear.dualBilinear).trans
    ((norm_dualBilinear_le m.dualBilinear).trans (norm_dualBilinear_le m))

/-- **Bilinear norm of the second Arens extension.** Let `𝕜` be a nontrivially normed field.
Let `E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`, `E**` for
the continuous dual and bidual, with their operator norms. Let `m : E →L[𝕜] F →L[𝕜] G` be
a bounded bilinear map. `‖m.arensSecond‖≤‖m‖` in the iterated operator norms. -/
theorem norm_arensSecond_le (m : E →L[𝕜] F →L[𝕜] G) : ‖m.arensSecond‖ ≤ ‖m‖ := by
  calc
    ‖m.arensSecond‖ = ‖m.flip.arensFirst‖ := opNorm_flip m.flip.arensFirst
    _ ≤ ‖m.flip‖ := norm_arensFirst_le m.flip
    _ = ‖m‖ := opNorm_flip m

/-- **Pointwise norm bound for the first Arens extension.** Let `𝕜` be a nontrivially normed
field. Let `E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`,
`E**` for the continuous dual and bidual, with their operator norms. Let `m : E →L[𝕜] F
→L[𝕜] G` be a bounded bilinear map. for `p ∈ E**` and `q ∈ F**`, `‖m.arensFirst p
q‖≤‖m‖*‖p‖*‖q‖`. -/
theorem norm_arensFirst_apply_le (m : E →L[𝕜] F →L[𝕜] G)
    (p : StrongDual 𝕜 (StrongDual 𝕜 E))
    (q : StrongDual 𝕜 (StrongDual 𝕜 F)) :
    ‖m.arensFirst p q‖ ≤ ‖m‖ * ‖p‖ * ‖q‖ := by
  exact (m.arensFirst.le_opNorm₂ p q).trans <| by
    gcongr
    exact norm_arensFirst_le m

/-- **Pointwise norm bound for the second Arens extension.** Let `𝕜` be a nontrivially normed
field. Let `E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`,
`E**` for the continuous dual and bidual, with their operator norms. Let `m : E →L[𝕜] F
→L[𝕜] G` be a bounded bilinear map. for `p ∈ E**` and `q ∈ F**`, `‖m.arensSecond p
q‖≤‖m‖*‖p‖*‖q‖`. -/
theorem norm_arensSecond_apply_le (m : E →L[𝕜] F →L[𝕜] G)
    (p : StrongDual 𝕜 (StrongDual 𝕜 E))
    (q : StrongDual 𝕜 (StrongDual 𝕜 F)) :
    ‖m.arensSecond p q‖ ≤ ‖m‖ * ‖p‖ * ‖q‖ := by
  exact (m.arensSecond.le_opNorm₂ p q).trans <| by
    gcongr
    exact norm_arensSecond_le m

/-- **First Arens extension on evaluation vectors.** Let `𝕜` be a nontrivially normed field.
Let `E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`, `E**` for
the continuous dual and bidual, with their operator norms. Let `m : E →L[𝕜] F →L[𝕜] G` be
a bounded bilinear map. let `J_E(x)(φ)=φ(x)` and similarly define `J_F,J_G`. Then
`m.arensFirst (J_E x) (J_F y)=J_G(m x y)` for `x ∈ E`, `y ∈ F`. -/
@[simp] theorem arensFirst_inclusion (m : E →L[𝕜] F →L[𝕜] G) (x : E) (y : F) :
    m.arensFirst (NormedSpace.inclusionInDoubleDual 𝕜 E x)
      (NormedSpace.inclusionInDoubleDual 𝕜 F y) =
        NormedSpace.inclusionInDoubleDual 𝕜 G (m x y) := by
  ext phi
  rfl

/-- **Second Arens extension on evaluation vectors.** Let `𝕜` be a nontrivially normed field.
Let `E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`, `E**` for
the continuous dual and bidual, with their operator norms. Let `m : E →L[𝕜] F →L[𝕜] G` be
a bounded bilinear map. for evaluation maps `J_E(x)(φ)=φ(x)` and `J_F,J_G` defined in the
same way, `m.arensSecond (J_E x) (J_F y)=J_G(m x y)`. -/
@[simp] theorem arensSecond_inclusion (m : E →L[𝕜] F →L[𝕜] G) (x : E) (y : F) :
    m.arensSecond (NormedSpace.inclusionInDoubleDual 𝕜 E x)
      (NormedSpace.inclusionInDoubleDual 𝕜 F y) =
        NormedSpace.inclusionInDoubleDual 𝕜 G (m x y) := by
  ext phi
  rfl

/-- **Weak-star continuity in the first Arens variable.** Let `𝕜` be a nontrivially normed
field. Let `E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`,
`E**` for the continuous dual and bidual, with their operator norms. Let `m : E →L[𝕜] F
→L[𝕜] G` be a bounded bilinear map. for fixed `q ∈ F**`, the map `p ↦ m.arensFirst p q` is
continuous from `E**` with `σ(E**,E*)` to `G**` with `σ(G**,G*)`. -/
theorem continuous_arensFirst_weakDual_left (m : E →L[𝕜] F →L[𝕜] G)
    (q : StrongDual 𝕜 (StrongDual 𝕜 F)) :
    Continuous (fun p : WeakDual 𝕜 (StrongDual 𝕜 E) =>
      StrongDual.toWeakDual (m.arensFirst p.toStrongDual q)) := by
  apply WeakDual.continuous_of_continuous_eval
  intro phi
  change Continuous (fun p : WeakDual 𝕜 (StrongDual 𝕜 E) =>
    p (m.dualBilinear.dualBilinear q phi))
  exact WeakDual.eval_continuous _

/-- **Weak-star continuity in the second Arens variable.** Let `𝕜` be a nontrivially normed
field. Let `E,F,G` be seminormed `𝕜`-spaces in independent universes, and write `E*`,
`E**` for the continuous dual and bidual, with their operator norms. Let `m : E →L[𝕜] F
→L[𝕜] G` be a bounded bilinear map. for fixed `p ∈ E**`, the map `q ↦ m.arensSecond p q`
is continuous from `F**` with `σ(F**,F*)` to `G**` with `σ(G**,G*)`. -/
theorem continuous_arensSecond_weakDual_right (m : E →L[𝕜] F →L[𝕜] G)
    (p : StrongDual 𝕜 (StrongDual 𝕜 E)) :
    Continuous (fun q : WeakDual 𝕜 (StrongDual 𝕜 F) =>
      StrongDual.toWeakDual (m.arensSecond p q.toStrongDual)) := by
  apply WeakDual.continuous_of_continuous_eval
  intro phi
  change Continuous (fun q : WeakDual 𝕜 (StrongDual 𝕜 F) =>
    q (m.flip.dualBilinear.dualBilinear p phi))
  exact WeakDual.eval_continuous _

end ContinuousLinearMap

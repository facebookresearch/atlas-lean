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
# Bounded dual transposes and the two Arens extensions

For an actual continuous bilinear map `m : E →L[𝕜] F →L[𝕜] G`, bounded
precomposition gives `(phi, x, y) ↦ phi (m x y)`. Three successive dual
transposes define its first Arens extension on the original strong biduals.
Flipping the original map and the resulting extension gives the second.

The dual norms, evaluations and named weak-star views are Mathlib's existing
ones. In particular, multiplication in a nonunital normed algebra supplies
`m` directly through `ContinuousLinearMap.mul`. The two extensions retain
the original order of the coefficient multiplication. Associativity, Arens
regularity, involution, a unit and a C-star identity are later prerequisites.
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

/-- The original operator seminorm structure on an actual continuous dual. -/
local instance arensDualSeminormed : SeminormedAddCommGroup (StrongDual 𝕜 G) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

/-- The existing scalar action and norm bound on that same continuous dual. -/
local instance arensDualNormedSpace : NormedSpace 𝕜 (StrongDual 𝕜 G) :=
  ContinuousLinearMap.toNormedSpace

/-- The original operator seminorm on maps into an actual continuous dual. -/
local instance arensDualTargetSeminormed : SeminormedAddCommGroup (E →L[𝕜] StrongDual 𝕜 F) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

/-- The existing normed scalar action on those actual dual-target maps. -/
local instance arensDualTargetNormedSpace : NormedSpace 𝕜 (E →L[𝕜] StrongDual 𝕜 F) :=
  ContinuousLinearMap.toNormedSpace

/-- Continuity of addition for the same inherited operator topology. -/
local instance arensDualTargetTopologicalAddGroup : IsTopologicalAddGroup (E →L[𝕜] StrongDual 𝕜 F) :=
  ContinuousLinearMap.isTopologicalAddGroup

/-- The original operator seminorm on the ordinary maps used by composition. -/
local instance arensMapSeminormed : SeminormedAddCommGroup (F →L[𝕜] G) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

/-- The existing scalar action on those original ordinary maps. -/
local instance arensMapNormedSpace : NormedSpace 𝕜 (F →L[𝕜] G) :=
  ContinuousLinearMap.toNormedSpace

/-- Addition is continuous for the original ordinary operator topology. -/
local instance arensMapTopologicalAddGroup : IsTopologicalAddGroup (F →L[𝕜] G) :=
  ContinuousLinearMap.isTopologicalAddGroup

/-- The original iterated operator seminorm on the actual second dual. -/
local instance arensBidualSeminormed : SeminormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

/-- The stock scalar action on the original second dual and its unchanged norm. -/
local instance arensBidualNormedSpace : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toNormedSpace

/-- The original operator seminorm on maps between the actual second duals. -/
local instance arensBidualMapSeminormed : SeminormedAddCommGroup
    (StrongDual 𝕜 (StrongDual 𝕜 F) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 G)) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

/-- The existing scalar action on those second-dual operator maps. -/
local instance arensBidualMapNormedSpace : NormedSpace 𝕜
    (StrongDual 𝕜 (StrongDual 𝕜 F) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 G)) :=
  ContinuousLinearMap.toNormedSpace

/-- Continuity of addition for the original second-dual operator topology. -/
local instance arensBidualMapTopologicalAddGroup : IsTopologicalAddGroup
    (StrongDual 𝕜 (StrongDual 𝕜 F) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 G)) :=
  ContinuousLinearMap.isTopologicalAddGroup

/-- Bounded dual precomposition with the literal formula `phi (m x y)`.
The three coefficient-space universes are independent, and zero spaces are allowed. -/
noncomputable def dualBilinear (m : E →L[𝕜] F →L[𝕜] G) :
    StrongDual 𝕜 G →L[𝕜] E →L[𝕜] StrongDual 𝕜 F :=
  ((compL 𝕜 F G 𝕜).flip.comp m).flip

/-- Evaluation of the bounded dual transpose uses the original bilinear value. -/
@[simp] theorem dualBilinear_apply (m : E →L[𝕜] F →L[𝕜] G)
    (phi : StrongDual 𝕜 G) (x : E) (y : F) :
    m.dualBilinear phi x y = phi (m x y) := rfl

/-- Dual precomposition does not increase the original bilinear operator norm. -/
theorem norm_dualBilinear_le (m : E →L[𝕜] F →L[𝕜] G) :
    ‖m.dualBilinear‖ ≤ ‖m‖ := by
  calc
    ‖m.dualBilinear‖ = ‖(compL 𝕜 F G 𝕜).flip.comp m‖ :=
      opNorm_flip ((compL 𝕜 F G 𝕜).flip.comp m)
    _ ≤ ‖(compL 𝕜 F G 𝕜).flip‖ * ‖m‖ := opNorm_comp_le (compL 𝕜 F G 𝕜).flip m
    _ = ‖compL 𝕜 F G 𝕜‖ * ‖m‖ := by rw [opNorm_flip]
    _ ≤ 1 * ‖m‖ := mul_le_mul_of_nonneg_right (norm_compL_le 𝕜 F G 𝕜) (norm_nonneg m)
    _ = ‖m‖ := one_mul _

/-- The actual transposed functional has the product bound in the original dual norm. -/
theorem norm_dualBilinear_apply_le (m : E →L[𝕜] F →L[𝕜] G)
    (phi : StrongDual 𝕜 G) (x : E) :
    ‖m.dualBilinear phi x‖ ≤ ‖m‖ * ‖phi‖ * ‖x‖ := by
  exact (m.dualBilinear.le_opNorm₂ phi x).trans <| by
    gcongr
    exact norm_dualBilinear_le m

/-- The first Arens extension on the original iterated continuous duals.
Its outer evaluation is by the first bidual variable. -/
noncomputable def arensFirst (m : E →L[𝕜] F →L[𝕜] G) :
    StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜]
      StrongDual 𝕜 (StrongDual 𝕜 F) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 G) :=
  m.dualBilinear.dualBilinear.dualBilinear

/-- The second Arens extension preserves the original bilinear order while
putting the second bidual variable in the outer evaluation. -/
noncomputable def arensSecond (m : E →L[𝕜] F →L[𝕜] G) :
    StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜]
      StrongDual 𝕜 (StrongDual 𝕜 F) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 G) :=
  m.flip.arensFirst.flip

/-- The literal first Arens evaluation, using an actual bounded iterated dual action. -/
@[simp] theorem arensFirst_apply (m : E →L[𝕜] F →L[𝕜] G)
    (p : StrongDual 𝕜 (StrongDual 𝕜 E))
    (q : StrongDual 𝕜 (StrongDual 𝕜 F)) (phi : StrongDual 𝕜 G) :
    m.arensFirst p q phi = p (m.dualBilinear.dualBilinear q phi) := rfl

/-- The literal second Arens evaluation, with the same original multiplication order. -/
@[simp] theorem arensSecond_apply (m : E →L[𝕜] F →L[𝕜] G)
    (p : StrongDual 𝕜 (StrongDual 𝕜 E))
    (q : StrongDual 𝕜 (StrongDual 𝕜 F)) (phi : StrongDual 𝕜 G) :
    m.arensSecond p q phi = q (m.flip.dualBilinear.dualBilinear p phi) := rfl

/-- The first Arens bilinear map is bounded by the norm of the original map. -/
theorem norm_arensFirst_le (m : E →L[𝕜] F →L[𝕜] G) : ‖m.arensFirst‖ ≤ ‖m‖ :=
  (norm_dualBilinear_le m.dualBilinear.dualBilinear).trans
    ((norm_dualBilinear_le m.dualBilinear).trans (norm_dualBilinear_le m))

/-- The second Arens bilinear map has the same original operator norm bound. -/
theorem norm_arensSecond_le (m : E →L[𝕜] F →L[𝕜] G) : ‖m.arensSecond‖ ≤ ‖m‖ := by
  calc
    ‖m.arensSecond‖ = ‖m.flip.arensFirst‖ := opNorm_flip m.flip.arensFirst
    _ ≤ ‖m.flip‖ := norm_arensFirst_le m.flip
    _ = ‖m‖ := opNorm_flip m

/-- The first Arens value has its original iterated-dual product norm bound. -/
theorem norm_arensFirst_apply_le (m : E →L[𝕜] F →L[𝕜] G)
    (p : StrongDual 𝕜 (StrongDual 𝕜 E))
    (q : StrongDual 𝕜 (StrongDual 𝕜 F)) :
    ‖m.arensFirst p q‖ ≤ ‖m‖ * ‖p‖ * ‖q‖ := by
  exact (m.arensFirst.le_opNorm₂ p q).trans <| by
    gcongr
    exact norm_arensFirst_le m

/-- The second Arens value has the analogous bound in the unchanged dual norm. -/
theorem norm_arensSecond_apply_le (m : E →L[𝕜] F →L[𝕜] G)
    (p : StrongDual 𝕜 (StrongDual 𝕜 E))
    (q : StrongDual 𝕜 (StrongDual 𝕜 F)) :
    ‖m.arensSecond p q‖ ≤ ‖m‖ * ‖p‖ * ‖q‖ := by
  exact (m.arensSecond.le_opNorm₂ p q).trans <| by
    gcongr
    exact norm_arensSecond_le m

/-- The first extension preserves the actual original evaluation embedding. -/
@[simp] theorem arensFirst_inclusion (m : E →L[𝕜] F →L[𝕜] G) (x : E) (y : F) :
    m.arensFirst (NormedSpace.inclusionInDoubleDual 𝕜 E x)
      (NormedSpace.inclusionInDoubleDual 𝕜 F y) =
        NormedSpace.inclusionInDoubleDual 𝕜 G (m x y) := by
  ext phi
  rfl

/-- The second extension also preserves that same original evaluation embedding. -/
@[simp] theorem arensSecond_inclusion (m : E →L[𝕜] F →L[𝕜] G) (x : E) (y : F) :
    m.arensSecond (NormedSpace.inclusionInDoubleDual 𝕜 E x)
      (NormedSpace.inclusionInDoubleDual 𝕜 F y) =
        NormedSpace.inclusionInDoubleDual 𝕜 G (m x y) := by
  ext phi
  rfl

/-- The first Arens product is weak-star continuous in its first variable,
using precisely the original first duals as the fixed pairing spaces. -/
theorem continuous_arensFirst_weakDual_left (m : E →L[𝕜] F →L[𝕜] G)
    (q : StrongDual 𝕜 (StrongDual 𝕜 F)) :
    Continuous (fun p : WeakDual 𝕜 (StrongDual 𝕜 E) =>
      StrongDual.toWeakDual (m.arensFirst p.toStrongDual q)) := by
  apply WeakDual.continuous_of_continuous_eval
  intro phi
  change Continuous (fun p : WeakDual 𝕜 (StrongDual 𝕜 E) =>
    p (m.dualBilinear.dualBilinear q phi))
  exact WeakDual.eval_continuous _

/-- The second Arens product is weak-star continuous in its second variable,
with the same named original-dual pairing and unchanged product values. -/
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

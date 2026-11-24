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

public import MathlibExt.Analysis.Normed.Operator.Arens
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Operator.Completeness

/-!
# Associative Arens products and the original normed bidual ring

Associativity of an actual bounded coefficient multiplication implies
associativity of both Arens products on the original strong bidual. The
first product then gives that same carrier a nonunital normed ring, with
the original addition, distance and dual operator norm. Its scalar action
is the original continuous-dual action. Coefficients may be incomplete or
zero; only scalar completeness is used in the separately stated completeness
of the constructed bidual topology.

The two Arens products use the stock normed-group structure of each continuous dual.
Involution, a unit, Arens regularity and the C-star identity remain separate
prerequisites.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

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

namespace ContinuousLinearMap

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {A : Type v} [SeminormedAddCommGroup A] [NormedSpace 𝕜 A]

/-- The original dual operator seminorm separates continuous functionals,
even when the coefficient space itself is only seminormed. The standard
separation constructor retains exactly the original norm, distance and topology. -/
local instance arensAlgebraDualNormedGroup : NormedAddCommGroup (StrongDual 𝕜 A) :=
  NormedAddCommGroup.ofSeparation <| by
    intro phi hphi
    ext a
    apply norm_eq_zero.mp
    have hle : ‖phi a‖ ≤ 0 := by
      simpa only [hphi, zero_mul] using phi.le_opNorm a
    exact le_antisymm hle (norm_nonneg (phi a))

/-- The first Arens product is associative when the original bounded bilinear
multiplication is associative; the proof uses only the actual dual evaluations. -/
theorem arensFirst_assoc (m : A →L[𝕜] A →L[𝕜] A)
    (h : ∀ a b c, m (m a b) c = m a (m b c))
    (p q r : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    m.arensFirst (m.arensFirst p q) r = m.arensFirst p (m.arensFirst q r) := by
  ext phi
  change p (m.dualBilinear.dualBilinear q (m.dualBilinear.dualBilinear r phi)) =
    p (m.dualBilinear.dualBilinear (m.arensFirst q r) phi)
  apply congrArg p
  ext a
  change q (m.dualBilinear (m.dualBilinear.dualBilinear r phi) a) =
    q (m.dualBilinear.dualBilinear r (m.dualBilinear phi a))
  apply congrArg q
  ext b
  change r (m.dualBilinear phi (m a b)) =
    r (m.dualBilinear (m.dualBilinear phi a) b)
  apply congrArg r
  ext c
  change phi (m (m a b) c) = phi (m a (m b c))
  exact congrArg phi (h a b c)

/-- The second Arens product is associative, with its original coefficient order. -/
theorem arensSecond_assoc (m : A →L[𝕜] A →L[𝕜] A)
    (h : ∀ a b c, m (m a b) c = m a (m b c))
    (p q r : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    m.arensSecond (m.arensSecond p q) r = m.arensSecond p (m.arensSecond q r) := by
  have hflip : ∀ a b c, m.flip (m.flip a b) c = m.flip a (m.flip b c) := by
    intro a b c
    change m c (m b a) = m (m c b) a
    exact (h c b a).symm
  change m.flip.arensFirst r (m.flip.arensFirst q p) =
    m.flip.arensFirst (m.flip.arensFirst r q) p
  exact (arensFirst_assoc m.flip hflip r q p).symm

/-- Addition in the first variable distributes through the first Arens product. -/
theorem arensFirst_add_left (m : A →L[𝕜] A →L[𝕜] A)
    (p q r : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    m.arensFirst (p + q) r = m.arensFirst p r + m.arensFirst q r :=
  congrArg (fun L : StrongDual 𝕜 (StrongDual 𝕜 A) →L[𝕜]
    StrongDual 𝕜 (StrongDual 𝕜 A) => L r) (m.arensFirst.map_add p q)

/-- Addition in the second variable distributes through the first Arens product. -/
theorem arensFirst_add_right (m : A →L[𝕜] A →L[𝕜] A)
    (p q r : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    m.arensFirst p (q + r) = m.arensFirst p q + m.arensFirst p r :=
  (m.arensFirst p).map_add q r

/-- Zero in the first variable gives the original zero bidual functional. -/
theorem arensFirst_zero_left (m : A →L[𝕜] A →L[𝕜] A)
    (q : StrongDual 𝕜 (StrongDual 𝕜 A)) : m.arensFirst 0 q = 0 := by
  ext phi
  rfl

/-- Zero in the second variable gives the same original zero functional. -/
theorem arensFirst_zero_right (m : A →L[𝕜] A →L[𝕜] A)
    (p : StrongDual 𝕜 (StrongDual 𝕜 A)) : m.arensFirst p 0 = 0 :=
  (m.arensFirst p).map_zero

/-- Scalar multiplication in the first bidual variable commutes with its product. -/
theorem arensFirst_smul_left (m : A →L[𝕜] A →L[𝕜] A) (c : 𝕜)
    (p q : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    m.arensFirst (c • p) q = c • m.arensFirst p q :=
  congrArg (fun L : StrongDual 𝕜 (StrongDual 𝕜 A) →L[𝕜]
    StrongDual 𝕜 (StrongDual 𝕜 A) => L q) (m.arensFirst.map_smul c p)

/-- Scalar multiplication in the second bidual variable commutes with its product. -/
theorem arensFirst_smul_right (m : A →L[𝕜] A →L[𝕜] A) (c : 𝕜)
    (p q : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    m.arensFirst p (c • q) = c • m.arensFirst p q :=
  (m.arensFirst p).map_smul c q

/-- Addition in the first variable distributes through the second Arens product. -/
theorem arensSecond_add_left (m : A →L[𝕜] A →L[𝕜] A)
    (p q r : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    m.arensSecond (p + q) r = m.arensSecond p r + m.arensSecond q r :=
  congrArg (fun L : StrongDual 𝕜 (StrongDual 𝕜 A) →L[𝕜]
    StrongDual 𝕜 (StrongDual 𝕜 A) => L r) (m.arensSecond.map_add p q)

/-- Addition in the second variable distributes through the second Arens product. -/
theorem arensSecond_add_right (m : A →L[𝕜] A →L[𝕜] A)
    (p q r : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    m.arensSecond p (q + r) = m.arensSecond p q + m.arensSecond p r :=
  (m.arensSecond p).map_add q r

/-- The second product has zero value when its first input is zero. -/
theorem arensSecond_zero_left (m : A →L[𝕜] A →L[𝕜] A)
    (q : StrongDual 𝕜 (StrongDual 𝕜 A)) : m.arensSecond 0 q = 0 :=
  congrArg (fun L : StrongDual 𝕜 (StrongDual 𝕜 A) →L[𝕜]
    StrongDual 𝕜 (StrongDual 𝕜 A) => L q) m.arensSecond.map_zero

/-- The second product has zero value when its second input is zero. -/
theorem arensSecond_zero_right (m : A →L[𝕜] A →L[𝕜] A)
    (p : StrongDual 𝕜 (StrongDual 𝕜 A)) : m.arensSecond p 0 = 0 := by
  ext phi
  rfl

/-- The original scalar action is linear in the first variable of the second product. -/
theorem arensSecond_smul_left (m : A →L[𝕜] A →L[𝕜] A) (c : 𝕜)
    (p q : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    m.arensSecond (c • p) q = c • m.arensSecond p q :=
  congrArg (fun L : StrongDual 𝕜 (StrongDual 𝕜 A) →L[𝕜]
    StrongDual 𝕜 (StrongDual 𝕜 A) => L q) (m.arensSecond.map_smul c p)

/-- The original scalar action is linear in the second variable of the second product. -/
theorem arensSecond_smul_right (m : A →L[𝕜] A →L[𝕜] A) (c : 𝕜)
    (p q : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    m.arensSecond p (c • q) = c • m.arensSecond p q :=
  (m.arensSecond p).map_smul c q

end ContinuousLinearMap

attribute [local instance] ContinuousLinearMap.arensAlgebraDualNormedGroup

namespace NormedSpace

variable (𝕜 : Type u) [NontriviallyNormedField 𝕜]
variable (A : Type v) [NonUnitalSeminormedRing A] [NormedSpace 𝕜 A]
variable [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- The actual first Arens multiplication is bounded by the unchanged dual norms. -/
theorem firstArens_mul_norm_le (p q : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    ‖(ContinuousLinearMap.mul 𝕜 A).arensFirst p q‖ ≤ ‖p‖ * ‖q‖ := by
  calc
    ‖(ContinuousLinearMap.mul 𝕜 A).arensFirst p q‖ ≤
        ‖ContinuousLinearMap.mul 𝕜 A‖ * ‖p‖ * ‖q‖ :=
      (ContinuousLinearMap.mul 𝕜 A).norm_arensFirst_apply_le p q
    _ ≤ 1 * ‖p‖ * ‖q‖ := by
      gcongr
      exact ContinuousLinearMap.opNorm_mul_le 𝕜 A
    _ = ‖p‖ * ‖q‖ := by rw [one_mul]

/-- The actual second Arens multiplication has the same original-norm bound. -/
theorem secondArens_mul_norm_le (p q : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    ‖(ContinuousLinearMap.mul 𝕜 A).arensSecond p q‖ ≤ ‖p‖ * ‖q‖ := by
  calc
    ‖(ContinuousLinearMap.mul 𝕜 A).arensSecond p q‖ ≤
        ‖ContinuousLinearMap.mul 𝕜 A‖ * ‖p‖ * ‖q‖ :=
      (ContinuousLinearMap.mul 𝕜 A).norm_arensSecond_apply_le p q
    _ ≤ 1 * ‖p‖ * ‖q‖ := by
      gcongr
      exact ContinuousLinearMap.opNorm_mul_le 𝕜 A
    _ = ‖p‖ * ‖q‖ := by rw [one_mul]

/-- The first Arens product gives the literal original bidual a nonunital ring.
Addition and additive inverses are the pre-existing continuous-dual operations. -/
@[instance_reducible] noncomputable def firstArensNonUnitalRing :
    NonUnitalRing (StrongDual 𝕜 (StrongDual 𝕜 A)) where
  __ := (inferInstance : AddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 A)))
  mul := fun p q => (ContinuousLinearMap.mul 𝕜 A).arensFirst p q
  mul_assoc := fun p q r => (ContinuousLinearMap.mul 𝕜 A).arensFirst_assoc
    (fun a b c => mul_assoc a b c) p q r
  left_distrib := fun p q r => (ContinuousLinearMap.mul 𝕜 A).arensFirst_add_right p q r
  right_distrib := fun p q r => (ContinuousLinearMap.mul 𝕜 A).arensFirst_add_left p q r
  zero_mul := (ContinuousLinearMap.mul 𝕜 A).arensFirst_zero_left
  mul_zero := (ContinuousLinearMap.mul 𝕜 A).arensFirst_zero_right

/-- The actual nonunital ring and the original iterated dual metric/norm form
its normed ring dictionary; no norm is transported from another model. -/
@[instance_reducible] noncomputable def firstArensNonUnitalNormedRing :
    NonUnitalNormedRing (StrongDual 𝕜 (StrongDual 𝕜 A)) where
  __ := firstArensNonUnitalRing 𝕜 A
  __ := (inferInstance : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 A)))
  dist_eq := fun p q => dist_eq_norm_neg_add p q
  norm_mul_le := firstArens_mul_norm_le 𝕜 A

/-- The constructed dictionary has precisely the original first Arens multiplication. -/
theorem firstArensNonUnitalNormedRing_mul
    (p q : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    letI := firstArensNonUnitalNormedRing 𝕜 A
    p * q = (ContinuousLinearMap.mul 𝕜 A).arensFirst p q := rfl

/-- Its norm is definitionally the original strong-bidual operator norm. -/
theorem firstArensNonUnitalNormedRing_norm (p : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    (firstArensNonUnitalNormedRing 𝕜 A).toNorm.norm p = ‖p‖ := rfl

/-- Original scalar multiplication and the first Arens multiplication have the tower law. -/
theorem firstArensIsScalarTower :
    letI := firstArensNonUnitalNormedRing 𝕜 A
    IsScalarTower 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 A)) (StrongDual 𝕜 (StrongDual 𝕜 A)) := by
  let _ := firstArensNonUnitalNormedRing 𝕜 A
  refine ⟨?_⟩
  intro c p q
  exact (ContinuousLinearMap.mul 𝕜 A).arensFirst_smul_left c p q

/-- Scalar and left multiplication commute on the same actual first-Arens ring. -/
theorem firstArensSMulCommClass :
    letI := firstArensNonUnitalNormedRing 𝕜 A
    SMulCommClass 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 A)) (StrongDual 𝕜 (StrongDual 𝕜 A)) := by
  let _ := firstArensNonUnitalNormedRing 𝕜 A
  refine ⟨?_⟩
  intro c p q
  exact ((ContinuousLinearMap.mul 𝕜 A).arensFirst_smul_right c p q).symm

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] in
/-- With complete scalars, the constructed ring has the original complete dual topology.
No completeness hypothesis is imposed on the coefficient algebra A. -/
theorem firstArensCompleteSpace [CompleteSpace 𝕜] :
    CompleteSpace (StrongDual 𝕜 (StrongDual 𝕜 A)) := by
  infer_instance

end NormedSpace

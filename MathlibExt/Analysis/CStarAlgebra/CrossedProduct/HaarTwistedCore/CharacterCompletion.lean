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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.CharacterSeminorm
public import MathlibExt.Analysis.CStarAlgebra.SeminormNonUnitalCompletionHom
public import Mathlib.Topology.DenseEmbedding

/-!
# The actual dual character automorphism on the original full Haar completion

Extend the computed raw character automorphism on the same original maximal
norm quotient/completion. Its actual bound is the proved gauge isometry.
Dense original coefficient images prove identity, composition and the
inverse character laws. No completed action, norm, model or equivalence
conclusion is supplied as a constructor premise.

Point-norm continuity in the character parameter is a separate required
constructor fact; no global dual action is selected before it is proved.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HaarTwistedCore

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (mu : Measure G) [mu.IsHaarMeasure] [mu.Regular] (alpha : PointNormCStarAction G A)

attribute [local instance] fullCovariantCompletionCStarAlgebra

/-- The original full-completion endomorphism induced by the actual raw character map. -/
def completedCharacterHom (chi : PontryaginDual G) :
    FullCovariantCompletion mu alpha →⋆ₙₐ[ℂ] FullCovariantCompletion mu alpha := by
  let p := maximalCStarSeminorm mu alpha
  letI : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  let f := p.toNonUnitalCompletion.comp (characterModulationEquiv mu alpha chi).toNonUnitalStarAlgHom
  exact p.fromNonUnitalCompletion f (fun x => by
    change ‖p.toNonUnitalCompletion (characterModulation mu alpha chi x)‖ ≤ p x
    rw [CStarSeminorm.norm_toNonUnitalCompletion, maximal_character_eq])

omit [mu.Regular] in
/-- The actual completed character map retains every original raw coefficient value. -/
@[simp]
theorem completedCharacterHom_apply (chi : PontryaginDual G) (f : Carrier mu alpha) :
    completedCharacterHom mu alpha chi (toFullCovariantCompletion mu alpha f) =
      toFullCovariantCompletion mu alpha (characterModulation mu alpha chi f) := by
  let p := maximalCStarSeminorm mu alpha
  let : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  exact p.fromNonUnitalCompletion_apply
    (p.toNonUnitalCompletion.comp (characterModulationEquiv mu alpha chi).toNonUnitalStarAlgHom)
    (fun x => by
      change ‖p.toNonUnitalCompletion (characterModulation mu alpha chi x)‖ ≤ p x
      rw [CStarSeminorm.norm_toNonUnitalCompletion, maximal_character_eq]) f

omit [mu.Regular] in
/-- Identity character gives the actual identity map on the same original completion. -/
theorem completedCharacterHom_one : completedCharacterHom mu alpha 1 = NonUnitalStarAlgHom.id ℂ _ := by
  have := NonUnitalStarAlgHom.instContinuousLinearMapClassComplex
    (F := FullCovariantCompletion mu alpha →⋆ₙₐ[ℂ] FullCovariantCompletion mu alpha)
  apply NonUnitalStarAlgHom.ext
  intro x
  refine (denseRange_toFullCovariantCompletion mu alpha).induction_on x
    (isClosed_eq (map_continuous (completedCharacterHom mu alpha 1)) continuous_id) ?_
  intro f
  rw [completedCharacterHom_apply, characterModulation_one]
  rfl

omit [mu.Regular] in
/-- Actual completed character maps compose in the original character group order. -/
theorem completedCharacterHom_mul (chi eta : PontryaginDual G) :
    completedCharacterHom mu alpha (chi * eta) =
      (completedCharacterHom mu alpha chi).comp (completedCharacterHom mu alpha eta) := by
  have := NonUnitalStarAlgHom.instContinuousLinearMapClassComplex
    (F := FullCovariantCompletion mu alpha →⋆ₙₐ[ℂ] FullCovariantCompletion mu alpha)
  apply NonUnitalStarAlgHom.ext
  intro x
  refine (denseRange_toFullCovariantCompletion mu alpha).induction_on x
    (isClosed_eq (map_continuous (completedCharacterHom mu alpha (chi * eta)))
      ((map_continuous (completedCharacterHom mu alpha chi)).comp
        (map_continuous (completedCharacterHom mu alpha eta)))) ?_
  intro f
  rw [completedCharacterHom_apply, characterModulation_mul_character]
  rw [NonUnitalStarAlgHom.comp_apply, completedCharacterHom_apply, completedCharacterHom_apply]

/-- The actual completed character map and its inverse character give a star-algebra equivalence. -/
def completedCharacterEquiv (chi : PontryaginDual G) :
    FullCovariantCompletion mu alpha ≃⋆ₐ[ℂ] FullCovariantCompletion mu alpha :=
  StarAlgEquiv.ofNonUnitalStarAlgHom (completedCharacterHom mu alpha chi)
    (completedCharacterHom mu alpha chi⁻¹)
    (by rw [← completedCharacterHom_mul, inv_mul_cancel, completedCharacterHom_one])
    (by rw [← completedCharacterHom_mul, mul_inv_cancel, completedCharacterHom_one])

omit [mu.Regular] in
/-- Every completed dual automorphism has the original raw scalar character value. -/
@[simp]
theorem completedCharacterEquiv_apply (chi : PontryaginDual G) (f : Carrier mu alpha) :
    completedCharacterEquiv mu alpha chi (toFullCovariantCompletion mu alpha f) =
      toFullCovariantCompletion mu alpha (characterModulation mu alpha chi f) :=
  completedCharacterHom_apply mu alpha chi f

end HaarTwistedCore

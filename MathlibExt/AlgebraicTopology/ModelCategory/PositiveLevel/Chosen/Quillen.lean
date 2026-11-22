/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.Chosen.Positive

/-!
# Every original positive base and finite-action free adjunction is Quillen

The given chosen cofibrations contain actual projective cofibrations. Hence
the original free Sigma_n input is left Quillen. Its complete original
free/evaluation composite gives the original free R-module at degree n; the
right evaluation functor is literally the original degree evaluation.
-/

set_option autoImplicit false
noncomputable section
universe w v u

open CategoryTheory Limits MorphismProperty MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj MonoidalClosed

namespace HomotopicalAlgebra.PositiveLevelModel.Chosen

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [ModelCategory C]
  [HasColimitsOfSize.{w, w} C]

local instance quillenBaseSmallColimits : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, w, w} C

variable (models : ChosenActionModels.{w} C)

/-- The actual base free Sigma_n arrow belongs to the literal projective cofibrations and thus the chosen cofibrations.
-/
theorem actionBaseFree_preservesCofibrations (n : ℕ) :
    let _ : ModelCategory (degreeActionCategory (C := C) n) := models.model n
    PreservesCofibrations (evaluationLeftAdjoint C (SingleObj.star (Equiv.Perm (Fin n)))) := by
  let _ : ModelCategory (degreeActionCategory (C := C) n) := models.model n
  change PreservesCofibrations (evaluationLeftAdjoint C (SingleObj.star (Equiv.Perm (Fin n))))
  intro A B i hi
  apply models.projective_cofibrations_le n
  intro X Y p hp
  apply (Adjunction.hasLiftingProperty_iff
    (evaluationAdjunctionRight C (SingleObj.star (Equiv.Perm (Fin n)))) i p).mpr
  exact ((trivialFibrations_llp C).symm.le i hi) _ (hp (SingleObj.star (Equiv.Perm (Fin n))))

/-- The original actual base free/evaluation adjunction is Quillen for each of the genuine chosen Sigma_n models. -/
theorem actionBaseFree_isQuillenAdjunction (n : ℕ) :
    let _ : ModelCategory (degreeActionCategory (C := C) n) := models.model n
    (evaluationAdjunctionRight C (SingleObj.star (Equiv.Perm (Fin n)))).IsQuillenAdjunction := by
  let _ : ModelCategory (degreeActionCategory (C := C) n) := models.model n
  refine ⟨actionBaseFree_preservesCofibrations models n, ?_⟩
  intro A B i hi
  refine ⟨actionBaseFree_preservesCofibrations models n i hi.1, ?_⟩
  change (models.model n).categoryWithWeakEquivalences.weakEquivalences
    ((evaluationLeftAdjoint C (SingleObj.star (Equiv.Perm (Fin n)))).map i)
  rw [models.weak_eq n]
  intro a
  let tau : Discrete.functor (fun _ : SingleObj.star (Equiv.Perm (Fin n)) ⟶ a => A) ⟶
      Discrete.functor (fun _ : SingleObj.star (Equiv.Perm (Fin n)) ⟶ a => B) :=
    Discrete.natTrans (fun _ => i)
  have ht : trivialCofibrations C (colimMap tau) := MorphismProperty.colimMap tau (fun _ => hi)
  exact ht.2

variable [SymmetricCategory C] [MonoidalClosed C] [HasLimitsOfSize.{w, w} C]
  [IsLocallyPresentable.{w} C]
  (small : PrettySmallSource.{w} C) (hm : HMonoidality C)

/-- The original canonical Day structure in the free and evaluation adjunctions. -/
local instance quillenDayMonoidal : MonoidalCategory (DayFunctor I C) := inferInstance
variable (R : DayFunctor I C) [MonObj R]

/-- Every original positive base free R-module/evaluation pair is Quillen, with no scalar or unit cofibrancy assumption.
-/
theorem positive_baseFreeEvaluation_isQuillenAdjunction (n : ℕ) (hn : 0 < n) :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := positiveModelCategory models small hm R
    (CategoryTheory.Mod.dayFreeAtEvaluationAdjunction R (CategoryTheory.Operad.SmallFinBijGroupoid.card
        n)).IsQuillenAdjunction := by
  let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := positiveModelCategory models small hm R
  let _ : ModelCategory (degreeActionCategory (C := C) n) := models.model n
  let _ : (degreeActionAdjunction R n).IsQuillenAdjunction :=
    positive_freeEvaluation_isQuillenAdjunction models small hm R n hn
  let _ : (evaluationAdjunctionRight C (SingleObj.star (Equiv.Perm (Fin n)))).IsQuillenAdjunction :=
    actionBaseFree_isQuillenAdjunction models n
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Y f hf
    have ha := Adjunction.IsQuillenAdjunction.preservesFibrations (adj := degreeActionAdjunction R n) f hf
    exact Adjunction.IsQuillenAdjunction.preservesFibrations
      (adj := evaluationAdjunctionRight C (SingleObj.star (Equiv.Perm (Fin n)))) _ ha
  · intro X Y f hf
    have ha := Adjunction.IsQuillenAdjunction.preservesTrivialFibrations (adj := degreeActionAdjunction R n) f hf
    exact Adjunction.IsQuillenAdjunction.preservesTrivialFibrations
      (adj := evaluationAdjunctionRight C (SingleObj.star (Equiv.Perm (Fin n)))) _ ha

end HomotopicalAlgebra.PositiveLevelModel.Chosen

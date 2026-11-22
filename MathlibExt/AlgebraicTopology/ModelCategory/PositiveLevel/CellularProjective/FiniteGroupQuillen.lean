/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.FreeActions.Basic
import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.CellularProjective.Positive
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Factorization

/-!
# Actual finite projective group models and positive free action adjunctions

The actual base generating datum constructs the existing projective model on
every genuine Sigma_n functor category. No local presentability or pretty
smallness is required. Evaluation of the original positive R-module model
is right Quillen into each of those actual projective action models.
-/

set_option autoImplicit false
noncomputable section
universe w v u

open CategoryTheory Limits MorphismProperty MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj MonoidalClosed

namespace HomotopicalAlgebra.PositiveLevelModel

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

/-- The genuine finite projective action model is the existing source-generated functor model. -/
@[instance_reducible]
def finiteGroupModelCategory (n : ℕ) : ModelCategory (degreeActionCategory (C := C) n) :=
  FunctorProjective.modelCategory.{w, 0, 0, u, v} (J := degreeActionIndex n) d

/-- The returned genuine projective weak equivalences are the original underlying weak equivalences. -/
theorem finiteGroup_weakEquivalences_eq (n : ℕ) :
    let _ : ModelCategory (degreeActionCategory (C := C) n) := finiteGroupModelCategory d n
    weakEquivalences (degreeActionCategory (C := C) n) =
      (weakEquivalences C).functorCategory (degreeActionIndex n) :=
  FunctorProjective.weakEquivalences_eq.{w, 0, 0, u, v} (J := degreeActionIndex n) d

/-- The actual projective fibrations are precisely the original underlying fibrations. -/
theorem finiteGroup_fibrations_eq (n : ℕ) :
    let _ : ModelCategory (degreeActionCategory (C := C) n) := finiteGroupModelCategory d n
    fibrations (degreeActionCategory (C := C) n) =
      (fibrations C).functorCategory (degreeActionIndex n) :=
  FunctorProjective.fibrations_eq.{w, 0, 0, u, v} (J := degreeActionIndex n) d

/-- The complete projective trivial-fibration class retains the original underlying intersection. -/
theorem finiteGroup_trivialFibrations_eq (n : ℕ) :
    let _ : ModelCategory (degreeActionCategory (C := C) n) := finiteGroupModelCategory d n
    trivialFibrations (degreeActionCategory (C := C) n) =
      (trivialFibrations C).functorCategory (degreeActionIndex n) :=
  FunctorProjective.trivialFibrations_eq.{w, 0, 0, u, v} (J := degreeActionIndex n) d

/-- The genuine projective cofibrations are exactly the source lifting definition. -/
theorem finiteGroup_cofibrations_eq (n : ℕ) :
    let _ : ModelCategory (degreeActionCategory (C := C) n) := finiteGroupModelCategory d n
    cofibrations (degreeActionCategory (C := C) n) =
      ((trivialFibrations C).functorCategory (degreeActionIndex n)).llp := by
  let _ : ModelCategory (degreeActionCategory (C := C) n) := finiteGroupModelCategory d n
  change cofibrations (degreeActionCategory (C := C) n) = _
  rw [← trivialFibrations_llp (degreeActionCategory (C := C) n), finiteGroup_trivialFibrations_eq d n]

/-- The complete projective trivial-cofibration class is the ordinary source left class. -/
theorem finiteGroup_trivialCofibrations_eq (n : ℕ) :
    let _ : ModelCategory (degreeActionCategory (C := C) n) := finiteGroupModelCategory d n
    trivialCofibrations (degreeActionCategory (C := C) n) =
      ((fibrations C).functorCategory (degreeActionIndex n)).llp := by
  let _ : ModelCategory (degreeActionCategory (C := C) n) := finiteGroupModelCategory d n
  change trivialCofibrations (degreeActionCategory (C := C) n) = _
  rw [← fibrations_llp (degreeActionCategory (C := C) n), finiteGroup_fibrations_eq d n]

variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]
  [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{0, 0} C] [LocallySmall.{w} C]
  (h : CellularSource d)

local instance finiteGroupBaseSmallColimits : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, w, w} C
/-- The canonical Day structure used by the original finite group adjunctions. -/
local instance finiteGroupDayMonoidal : MonoidalCategory (DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid C) :=
    inferInstance

variable (R : DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid C) [MonObj R]
  (hR : ∀ n : ℕ, IsCofibrant (R.functor.obj (CategoryTheory.Operad.SmallFinBijGroupoid.card n)))

namespace CellularProjective

/-- Every genuine positive finite-action free/evaluation pair is Quillen for the actual projective R-module model. -/
theorem positive_actionFreeEvaluation_isQuillenAdjunction (n : ℕ) (hn : 0 < n) :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid C) R) :=
      positiveModelCategory d h R hR
    let _ : ModelCategory (degreeActionCategory (C := C) n) := finiteGroupModelCategory d n
    (degreeActionAdjunction R n).IsQuillenAdjunction := by
  let _ : ModelCategory (CategoryTheory.Mod (DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid C) R) :=
    positiveModelCategory d h R hR
  let _ : ModelCategory (degreeActionCategory (C := C) n) := finiteGroupModelCategory d n
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Y f hf
    rw [finiteGroup_fibrations_eq d n]
    intro a
    exact (positive_fibration_iff d h R hR f).mp hf n hn
  · intro X Y f hf
    rw [finiteGroup_trivialFibrations_eq d n]
    intro a
    have ht := (positive_trivialFibrations_eq d h R hR).le f hf
    exact (positiveProperty_iff R (trivialFibrations C) f).mp ht n hn

end CellularProjective
end HomotopicalAlgebra.PositiveLevelModel

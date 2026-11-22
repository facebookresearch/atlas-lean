/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.Chosen.Positive

/-!
# Actual maps and zero components of both positive source factorizations

Every original module Arrow and every original Arrow square are retained.
Both small-object left maps have isomorphic degree zero; their right maps
are the original caller's zero map conjugated by those actual left isomorphisms.
-/

set_option autoImplicit false
noncomputable section
universe w v u

open CategoryTheory Limits MorphismProperty MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj MonoidalClosed

namespace HomotopicalAlgebra.PositiveLevelModel.Chosen

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [ModelCategory C] [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{w, w} C]
  [IsLocallyPresentable.{w} C]

local instance factorChosenBaseSmallColimits : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, w, w} C
/-- The canonical Day structure used by the original chosen factor maps. -/
local instance factorChosenDayMonoidal : MonoidalCategory (DayFunctor I C) := inferInstance

variable (models : ChosenActionModels.{w} C) (small : PrettySmallSource.{w} C) (hm : HMonoidality C)
  (R : DayFunctor I C) [MonObj R]

/-- The actual positive I factor maps factor every original module arrow. -/
theorem positiveIFactor_fac (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) :
    (positiveCofibrantFactorizationData models small hm R).i.app f ≫
      (positiveCofibrantFactorizationData models small hm R).p.app f = f.hom :=
  (positiveCofibrantFactorizationData models small hm R).fac_app

/-- The actual positive J factor maps factor the very same original caller arrow. -/
theorem positiveJFactor_fac (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) :
    (positiveFibrantFactorizationData models small hm R).i.app f ≫
      (positiveFibrantFactorizationData models small hm R).p.app f = f.hom :=
  (positiveFibrantFactorizationData models small hm R).fac_app

/-- Every original I factor equation retains the caller's exact original evaluated map in every degree. -/
theorem positiveIFactor_fac_component (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) (n : I) :
    (CategoryTheory.Mod.dayEvaluation R n).map ((positiveCofibrantFactorizationData models small hm R).i.app f) ≫
      (CategoryTheory.Mod.dayEvaluation R n).map ((positiveCofibrantFactorizationData models small hm R).p.app f) =
        (CategoryTheory.Mod.dayEvaluation R n).map f.hom := by
  rw [← Functor.map_comp, positiveIFactor_fac]

/-- Every original J factor equation retains that same caller's evaluated map at every degree, including zero. -/
theorem positiveJFactor_fac_component (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) (n : I) :
    (CategoryTheory.Mod.dayEvaluation R n).map ((positiveFibrantFactorizationData models small hm R).i.app f) ≫
      (CategoryTheory.Mod.dayEvaluation R n).map ((positiveFibrantFactorizationData models small hm R).p.app f) =
        (CategoryTheory.Mod.dayEvaluation R n).map f.hom := by
  rw [← Functor.map_comp, positiveJFactor_fac]

/-- The actual positive I small-object left map is an isomorphism at the original degree zero. -/
theorem positiveIFactor_zero_isIso (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) :
    IsIso ((zeroEvaluation R).map ((positiveCofibrantFactorizationData models small hm R).i.app f)) := by
  let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := positiveModelCategory models small hm R
  have hi := (positiveCofibrantFactorizationData models small hm R).hi f
  exact ((positive_cofibrations_eq_ordinary_zero models small hm R).le.trans inf_le_right) _ hi

/-- The actual positive J small-object left map also has its original degree-zero isomorphism. -/
theorem positiveJFactor_zero_isIso (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) :
    IsIso ((zeroEvaluation R).map ((positiveFibrantFactorizationData models small hm R).i.app f)) := by
  let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := positiveModelCategory models small hm R
  have hi : cofibrations (CategoryTheory.Mod (DayFunctor I C) R)
      ((positiveFibrantFactorizationData models small hm R).i.app f) :=
    ((positiveFibrantFactorizationData models small hm R).hi f).1
  exact ((positive_cofibrations_eq_ordinary_zero models small hm R).le.trans inf_le_right) _ hi

/-- The actual I right factor has precisely the caller's unrestricted zero map after the original left isomorphism. -/
theorem positiveIFactor_zero_right (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) :
    let _ : IsIso ((zeroEvaluation R).map ((positiveCofibrantFactorizationData models small hm R).i.app f)) :=
      positiveIFactor_zero_isIso models small hm R f
    (zeroEvaluation R).map ((positiveCofibrantFactorizationData models small hm R).p.app f) =
      inv ((zeroEvaluation R).map ((positiveCofibrantFactorizationData models small hm R).i.app f)) ≫
        (zeroEvaluation R).map f.hom := by
  let _ : IsIso ((zeroEvaluation R).map ((positiveCofibrantFactorizationData models small hm R).i.app f)) :=
    positiveIFactor_zero_isIso models small hm R f
  exact ((IsIso.inv_comp_eq _).mpr (positiveIFactor_fac_component models small hm R f
      (CategoryTheory.Operad.SmallFinBijGroupoid.card 0)).symm).symm

/-- The actual J right factor similarly retains the unrestricted caller zero map and the original J left isomorphism. -/
theorem positiveJFactor_zero_right (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) :
    let _ : IsIso ((zeroEvaluation R).map ((positiveFibrantFactorizationData models small hm R).i.app f)) :=
      positiveJFactor_zero_isIso models small hm R f
    (zeroEvaluation R).map ((positiveFibrantFactorizationData models small hm R).p.app f) =
      inv ((zeroEvaluation R).map ((positiveFibrantFactorizationData models small hm R).i.app f)) ≫
        (zeroEvaluation R).map f.hom := by
  let _ : IsIso ((zeroEvaluation R).map ((positiveFibrantFactorizationData models small hm R).i.app f)) :=
    positiveJFactor_zero_isIso models small hm R f
  exact ((IsIso.inv_comp_eq _).mpr (positiveJFactor_fac_component models small hm R f
      (CategoryTheory.Operad.SmallFinBijGroupoid.card 0)).symm).symm

/-- Every original Arrow square retains the actual I factor's left naturality word. -/
theorem positiveIFactor_i_naturality {f g : Arrow (CategoryTheory.Mod (DayFunctor I C) R)} (s : f ⟶ g) :
    s.left ≫ (positiveCofibrantFactorizationData models small hm R).i.app g =
      (positiveCofibrantFactorizationData models small hm R).i.app f ≫
        (positiveCofibrantFactorizationData models small hm R).Z.map s :=
  (positiveCofibrantFactorizationData models small hm R).i.naturality s

/-- Every original Arrow square retains the actual I factor's right naturality word. -/
theorem positiveIFactor_p_naturality {f g : Arrow (CategoryTheory.Mod (DayFunctor I C) R)} (s : f ⟶ g) :
    (positiveCofibrantFactorizationData models small hm R).Z.map s ≫
      (positiveCofibrantFactorizationData models small hm R).p.app g =
        (positiveCofibrantFactorizationData models small hm R).p.app f ≫ s.right :=
  (positiveCofibrantFactorizationData models small hm R).p.naturality s

/-- The actual J factor keeps the original complete left naturality word on every caller square. -/
theorem positiveJFactor_i_naturality {f g : Arrow (CategoryTheory.Mod (DayFunctor I C) R)} (s : f ⟶ g) :
    s.left ≫ (positiveFibrantFactorizationData models small hm R).i.app g =
      (positiveFibrantFactorizationData models small hm R).i.app f ≫
        (positiveFibrantFactorizationData models small hm R).Z.map s :=
  (positiveFibrantFactorizationData models small hm R).i.naturality s

/-- The actual J factor retains the original right naturality word on all original caller squares. -/
theorem positiveJFactor_p_naturality {f g : Arrow (CategoryTheory.Mod (DayFunctor I C) R)} (s : f ⟶ g) :
    (positiveFibrantFactorizationData models small hm R).Z.map s ≫
      (positiveFibrantFactorizationData models small hm R).p.app g =
        (positiveFibrantFactorizationData models small hm R).p.app f ≫ s.right :=
  (positiveFibrantFactorizationData models small hm R).p.naturality s

end HomotopicalAlgebra.PositiveLevelModel.Chosen

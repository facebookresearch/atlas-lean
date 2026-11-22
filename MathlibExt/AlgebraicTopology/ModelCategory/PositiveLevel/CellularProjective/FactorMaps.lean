/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.CellularProjective.Positive

/-!
# Actual maps and zero components of both positive source factorizations

Every original module Arrow and every original Arrow square are retained.
Both small-object left maps have isomorphic degree zero; their right maps
are the original caller's zero map conjugated by those actual left isomorphisms.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w v u

open CategoryTheory Limits MorphismProperty MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj MonoidalClosed

namespace HomotopicalAlgebra.PositiveLevelModel.CellularProjective

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [ModelCategory C] [IsClosedSymmetricMonoidalModelCategory C]
  [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{0, 0} C] [LocallySmall.{w} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (h : CellularSource d)

local instance factorBaseSmallColimits : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, w, w} C

variable (R : DayFunctor I C) [MonObj R]
  (hR : ∀ n : ℕ, IsCofibrant (R.functor.obj (CategoryTheory.Operad.SmallFinBijGroupoid.card n)))

/-- The actual positive I factor maps factor every original module arrow. -/
theorem positiveIFactor_fac (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) :
    (positiveCofibrantFactorizationData d h R hR).i.app f ≫
      (positiveCofibrantFactorizationData d h R hR).p.app f = f.hom :=
  (positiveCofibrantFactorizationData d h R hR).fac_app

/-- The actual positive J factor maps factor the very same original caller arrow. -/
theorem positiveJFactor_fac (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) :
    (positiveFibrantFactorizationData d h R hR).i.app f ≫
      (positiveFibrantFactorizationData d h R hR).p.app f = f.hom :=
  (positiveFibrantFactorizationData d h R hR).fac_app

/-- Every original I factor equation retains the caller's exact original evaluated map in every degree. -/
theorem positiveIFactor_fac_component (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) (n : I) :
    (CategoryTheory.Mod.dayEvaluation R n).map ((positiveCofibrantFactorizationData d h R hR).i.app f) ≫
      (CategoryTheory.Mod.dayEvaluation R n).map ((positiveCofibrantFactorizationData d h R hR).p.app f) =
        (CategoryTheory.Mod.dayEvaluation R n).map f.hom := by
  rw [← Functor.map_comp, positiveIFactor_fac]

/-- Every original J factor equation retains that same caller's evaluated map at every degree, including zero. -/
theorem positiveJFactor_fac_component (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) (n : I) :
    (CategoryTheory.Mod.dayEvaluation R n).map ((positiveFibrantFactorizationData d h R hR).i.app f) ≫
      (CategoryTheory.Mod.dayEvaluation R n).map ((positiveFibrantFactorizationData d h R hR).p.app f) =
        (CategoryTheory.Mod.dayEvaluation R n).map f.hom := by
  rw [← Functor.map_comp, positiveJFactor_fac]

/-- The actual positive I small-object left map is an isomorphism at the original degree zero. -/
theorem positiveIFactor_zero_isIso (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) :
    IsIso ((zeroEvaluation R).map ((positiveCofibrantFactorizationData d h R hR).i.app f)) := by
  let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := positiveModelCategory d h R hR
  have hi := (positiveCofibrantFactorizationData d h R hR).hi f
  exact ((positive_cofibrations_eq_ordinary_zero d h R hR).le.trans inf_le_right) _ hi

/-- The actual positive J small-object left map also has its original degree-zero isomorphism. -/
theorem positiveJFactor_zero_isIso (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) :
    IsIso ((zeroEvaluation R).map ((positiveFibrantFactorizationData d h R hR).i.app f)) := by
  let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := positiveModelCategory d h R hR
  have hi : cofibrations (CategoryTheory.Mod (DayFunctor I C) R)
      ((positiveFibrantFactorizationData d h R hR).i.app f) :=
    ((positiveFibrantFactorizationData d h R hR).hi f).1
  exact ((positive_cofibrations_eq_ordinary_zero d h R hR).le.trans inf_le_right) _ hi

/-- The actual I right factor has precisely the caller's unrestricted zero map after the original left isomorphism. -/
theorem positiveIFactor_zero_right (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) :
    let _ : IsIso ((zeroEvaluation R).map ((positiveCofibrantFactorizationData d h R hR).i.app f)) :=
      positiveIFactor_zero_isIso d h R hR f
    (zeroEvaluation R).map ((positiveCofibrantFactorizationData d h R hR).p.app f) =
      inv ((zeroEvaluation R).map ((positiveCofibrantFactorizationData d h R hR).i.app f)) ≫
        (zeroEvaluation R).map f.hom := by
  let _ : IsIso ((zeroEvaluation R).map ((positiveCofibrantFactorizationData d h R hR).i.app f)) :=
    positiveIFactor_zero_isIso d h R hR f
  exact ((IsIso.inv_comp_eq _).mpr (positiveIFactor_fac_component d h R hR f
      (CategoryTheory.Operad.SmallFinBijGroupoid.card 0)).symm).symm

/-- The actual J right factor similarly retains the unrestricted caller zero map and the original J left isomorphism. -/
theorem positiveJFactor_zero_right (f : Arrow (CategoryTheory.Mod (DayFunctor I C) R)) :
    let _ : IsIso ((zeroEvaluation R).map ((positiveFibrantFactorizationData d h R hR).i.app f)) :=
      positiveJFactor_zero_isIso d h R hR f
    (zeroEvaluation R).map ((positiveFibrantFactorizationData d h R hR).p.app f) =
      inv ((zeroEvaluation R).map ((positiveFibrantFactorizationData d h R hR).i.app f)) ≫
        (zeroEvaluation R).map f.hom := by
  let _ : IsIso ((zeroEvaluation R).map ((positiveFibrantFactorizationData d h R hR).i.app f)) :=
    positiveJFactor_zero_isIso d h R hR f
  exact ((IsIso.inv_comp_eq _).mpr (positiveJFactor_fac_component d h R hR f
      (CategoryTheory.Operad.SmallFinBijGroupoid.card 0)).symm).symm

/-- Every original Arrow square retains the actual I factor's left naturality word. -/
theorem positiveIFactor_i_naturality {f g : Arrow (CategoryTheory.Mod (DayFunctor I C) R)} (s : f ⟶ g) :
    s.left ≫ (positiveCofibrantFactorizationData d h R hR).i.app g =
      (positiveCofibrantFactorizationData d h R hR).i.app f ≫
        (positiveCofibrantFactorizationData d h R hR).Z.map s :=
  (positiveCofibrantFactorizationData d h R hR).i.naturality s

/-- Every original Arrow square retains the actual I factor's right naturality word. -/
theorem positiveIFactor_p_naturality {f g : Arrow (CategoryTheory.Mod (DayFunctor I C) R)} (s : f ⟶ g) :
    (positiveCofibrantFactorizationData d h R hR).Z.map s ≫
      (positiveCofibrantFactorizationData d h R hR).p.app g =
        (positiveCofibrantFactorizationData d h R hR).p.app f ≫ s.right :=
  (positiveCofibrantFactorizationData d h R hR).p.naturality s

/-- The actual J factor keeps the original complete left naturality word on every caller square. -/
theorem positiveJFactor_i_naturality {f g : Arrow (CategoryTheory.Mod (DayFunctor I C) R)} (s : f ⟶ g) :
    s.left ≫ (positiveFibrantFactorizationData d h R hR).i.app g =
      (positiveFibrantFactorizationData d h R hR).i.app f ≫
        (positiveFibrantFactorizationData d h R hR).Z.map s :=
  (positiveFibrantFactorizationData d h R hR).i.naturality s

/-- The actual J factor retains the original right naturality word on all original caller squares. -/
theorem positiveJFactor_p_naturality {f g : Arrow (CategoryTheory.Mod (DayFunctor I C) R)} (s : f ⟶ g) :
    (positiveFibrantFactorizationData d h R hR).Z.map s ≫
      (positiveFibrantFactorizationData d h R hR).p.app g =
        (positiveFibrantFactorizationData d h R hR).p.app f ≫ s.right :=
  (positiveFibrantFactorizationData d h R hR).p.naturality s

end HomotopicalAlgebra.PositiveLevelModel.CellularProjective

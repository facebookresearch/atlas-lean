/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFunctorialReplacements
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenPuppe
import MathlibExt.AlgebraicTopology.ModelCategory.LocalizationFibrantProducts

/-!
# The actual fibrant binary product in ordinary Ho

The proved model-localization product theorem retains the original Ho
product point and both actual projection maps. Uniqueness applies to the
same complete Ho maps. The original chosen lift and all cofibrancy/fibrancy
inputs needed for that lift remain explicit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u v

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.OrdinaryHoFibrantProduct

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X Y Z : C) [IsCofibrant X] [IsFibrant Y] [IsFibrant Z]

/-- The original product source projection fibration proves fibrancy of that SAME product. -/
theorem product_isFibrant : IsFibrant (Y ⨯ Z) :=
  isFibrant_of_fibration (prod.fst : Y ⨯ Z ⟶ Y)

omit [IsCofibrant X] in
/-- Both actual original Ho product projections jointly determine the SAME Ho map. -/
theorem hom_ext
    (f f' : (toHomotopyCategory C).obj X ⟶ (toHomotopyCategory C).obj (Y ⨯ Z))
    (hf : f ≫ (toHomotopyCategory C).map (prod.fst : Y ⨯ Z ⟶ Y) =
      f' ≫ (toHomotopyCategory C).map (prod.fst : Y ⨯ Z ⟶ Y))
    (hs : f ≫ (toHomotopyCategory C).map (prod.snd : Y ⨯ Z ⟶ Z) =
      f' ≫ (toHomotopyCategory C).map (prod.snd : Y ⨯ Z ⟶ Z)) : f = f' :=
  ModelLocalization.product_hom_ext (toHomotopyCategory C) Y Z f f' hf hs

/-- Every pair of complete original Ho maps is computed by the SAME actual original product lift. -/
def lift (f : (toHomotopyCategory C).obj X ⟶ (toHomotopyCategory C).obj Y)
    (h : (toHomotopyCategory C).obj X ⟶ (toHomotopyCategory C).obj Z) :
    (toHomotopyCategory C).obj X ⟶ (toHomotopyCategory C).obj (Y ⨯ Z) := by
  let a : X ⟶ Y := (map_surjective_of_isLocalization (toHomotopyCategory C) X Y f).choose
  let b : X ⟶ Z := (map_surjective_of_isLocalization (toHomotopyCategory C) X Z h).choose
  exact (toHomotopyCategory C).map (prod.lift a b)

/-- The original first projection reads back the entire original caller's first Ho map. -/
theorem lift_fst (f : (toHomotopyCategory C).obj X ⟶ (toHomotopyCategory C).obj Y)
    (h : (toHomotopyCategory C).obj X ⟶ (toHomotopyCategory C).obj Z) :
    lift X Y Z f h ≫ (toHomotopyCategory C).map (prod.fst : Y ⨯ Z ⟶ Y) = f := by
  unfold lift
  rw [← Functor.map_comp, prod.lift_fst]
  exact (map_surjective_of_isLocalization (toHomotopyCategory C) X Y f).choose_spec

/-- The original second projection reads back the entire original caller's second Ho map. -/
theorem lift_snd (f : (toHomotopyCategory C).obj X ⟶ (toHomotopyCategory C).obj Y)
    (h : (toHomotopyCategory C).obj X ⟶ (toHomotopyCategory C).obj Z) :
    lift X Y Z f h ≫ (toHomotopyCategory C).map (prod.snd : Y ⨯ Z ⟶ Z) = h := by
  unfold lift
  rw [← Functor.map_comp, prod.lift_snd]
  exact (map_surjective_of_isLocalization (toHomotopyCategory C) X Z h).choose_spec

end HomotopicalAlgebra.OrdinaryHoFibrantProduct

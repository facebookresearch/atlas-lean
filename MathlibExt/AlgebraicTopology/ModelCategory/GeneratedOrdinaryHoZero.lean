/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFunctorialReplacements
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenPuppe

/-!
# The original caller zero remains zero in ordinary Ho

The original Q and R maps compare every Ho object with actual cofibrant
and fibrant endpoints. The fundamental Hom lemma and the caller zero's
original universal properties prove both uniqueness laws. The resulting
zero object retains the actual original initial and terminal map functions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe w u v

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.GeneratedOrdinaryHoZero

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)

/-- The original caller terminal map is retained on every original Ho object. -/
def toZero (X : HomotopyCategory C) : X ⟶ (toHomotopyCategory C).obj Z := by
  rcases X with ⟨⟨X⟩⟩
  exact (toHomotopyCategory C).map (OrdinaryHoChosenPuppe.toZero Z hZ X)

/-- The original caller initial map is retained on every original Ho object. -/
def fromZero (X : HomotopyCategory C) : (toHomotopyCategory C).obj Z ⟶ X := by
  rcases X with ⟨⟨X⟩⟩
  exact (toHomotopyCategory C).map (OrdinaryHoChosenPuppe.fromZero Z hZ X)

include g hZ in
/-- The actual original R unit and original zero-source Hom lemma give uniqueness at every Ho target. -/
theorem from_unique (X : HomotopyCategory C) (f f' : (toHomotopyCategory C).obj Z ⟶ X) : f = f' := by
  rcases X with ⟨⟨X⟩⟩
  let : IsIso ((toHomotopyCategory C).map ((GeneratedFunctorialReplacements.unit g).app X)) :=
    Localization.inverts (toHomotopyCategory C) (weakEquivalences C) _
      (GeneratedFunctorialReplacements.unit_weak g X)
  apply (cancel_mono ((toHomotopyCategory C).map ((GeneratedFunctorialReplacements.unit g).app X))).mp
  let : IsFibrant ((GeneratedFunctorialReplacements.R g).obj X) :=
    GeneratedFunctorialReplacements.R_isFibrant g X
  exact (OrdinaryHoChosenPuppe.actualZeroHom_subsingleton Z hZ
    ((GeneratedFunctorialReplacements.R g).obj X)).elim _ _

include g hZ in
/-- The actual original Q counit and original zero-target universal property give uniqueness at every Ho source. -/
theorem to_unique (X : HomotopyCategory C) (f f' : X ⟶ (toHomotopyCategory C).obj Z) : f = f' := by
  rcases X with ⟨⟨X⟩⟩
  let : IsIso ((toHomotopyCategory C).map ((GeneratedFunctorialReplacements.counit g).app X)) :=
    Localization.inverts (toHomotopyCategory C) (weakEquivalences C) _
      (GeneratedFunctorialReplacements.counit_weak g X)
  apply (cancel_epi ((toHomotopyCategory C).map ((GeneratedFunctorialReplacements.counit g).app X))).mp
  let : IsCofibrant ((GeneratedFunctorialReplacements.Q g).obj X) :=
    GeneratedFunctorialReplacements.Q_isCofibrant g X
  let : IsFibrant Z :=
    (isFibrant_iff_of_isTerminal (𝟙 Z) hZ.isTerminal).mpr (by infer_instance)
  obtain ⟨a, ha⟩ := map_surjective_of_isLocalization (toHomotopyCategory C)
    ((GeneratedFunctorialReplacements.Q g).obj X) Z
    ((toHomotopyCategory C).map ((GeneratedFunctorialReplacements.counit g).app X) ≫ f)
  obtain ⟨b, hb⟩ := map_surjective_of_isLocalization (toHomotopyCategory C)
    ((GeneratedFunctorialReplacements.Q g).obj X) Z
    ((toHomotopyCategory C).map ((GeneratedFunctorialReplacements.counit g).app X) ≫ f')
  exact ha.symm.trans (((toHomotopyCategory C).congr_map (hZ.isTerminal.hom_ext a b)).trans hb)

include g hZ in
/-- Both earned original uniqueness laws make the SAME original caller zero a zero object in Ho. -/
theorem isZero : IsZero ((toHomotopyCategory C).obj Z) where
  unique_to X := ⟨{ default := fromZero Z hZ X, uniq := fun f => from_unique g Z hZ X f _ }⟩
  unique_from X := ⟨{ default := toZero Z hZ X, uniq := fun f => to_unique g Z hZ X f _ }⟩

end HomotopicalAlgebra.GeneratedOrdinaryHoZero

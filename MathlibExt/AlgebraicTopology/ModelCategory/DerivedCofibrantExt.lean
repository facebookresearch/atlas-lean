/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedReplacementConstruction
public import Mathlib.CategoryTheory.Localization.HasLocalization

/-!
# Equality of full derived transformations from actual cofibrant representatives

The actual chosen Q counit is weak at every original object. Its image and
all functor images are invertible. Naturality therefore extends equality on
the original cofibrant objects to equality of complete derived natural
transformations, including two, three and four variables.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v uD vD

open CategoryTheory

namespace HomotopicalAlgebra.GeneratedFunctorialReplacements

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D]

local notation "Ho" => MorphismProperty.Localization (weakEquivalences C)
local notation "π" => MorphismProperty.Q (weakEquivalences C)

/-- The exact chosen weak Q counits extend equality from every original cofibrant source. -/
theorem natTrans_ext_cofibrant (d : Data (C := C)) {F G : Ho ⥤ D} {τ τ' : F ⟶ G}
    (h : ∀ (X : C) [IsCofibrant X], τ.app ((π).obj X) = τ'.app ((π).obj X)) : τ = τ' := by
  apply Localization.natTrans_ext π (weakEquivalences C)
  intro X
  let _ : IsCofibrant (d.Q.obj X) := d.q_cofibrant X
  let qX : d.Q.obj X ⟶ X := d.q.app X
  let _ : IsIso ((π).map qX) := Localization.inverts π (weakEquivalences C) qX
    (d.q_trivialFibration X).2
  apply (cancel_epi (F.map ((π).map qX))).mp
  rw [τ.naturality, τ'.naturality, h (d.Q.obj X)]

/-- Equality on the same two actual cofibrant source objects proves equality of full bifunctor maps.
-/
theorem natTrans₂_ext_cofibrant (d : Data (C := C)) {F G : Ho ⥤ Ho ⥤ D} {τ τ' : F ⟶ G}
    (h : ∀ (X Y : C) [IsCofibrant X] [IsCofibrant Y],
      (τ.app ((π).obj X)).app ((π).obj Y) = (τ'.app ((π).obj X)).app ((π).obj Y)) : τ = τ' := by
  apply natTrans_ext_cofibrant d
  intro X _
  apply natTrans_ext_cofibrant d
  intro Y _
  exact h X Y

/-- The same original counit naturalities extend every three-variable source equality. -/
theorem natTrans₃_ext_cofibrant (d : Data (C := C)) {F G : Ho ⥤ Ho ⥤ Ho ⥤ D} {τ τ' : F ⟶ G}
    (h : ∀ (X Y Z : C) [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z],
      ((τ.app ((π).obj X)).app ((π).obj Y)).app ((π).obj Z) =
        ((τ'.app ((π).obj X)).app ((π).obj Y)).app ((π).obj Z)) : τ = τ' := by
  apply natTrans_ext_cofibrant d
  intro X _
  apply natTrans₂_ext_cofibrant d
  intro Y Z _ _
  exact h X Y Z

/-- Four-variable coherence on actual cofibrant objects is coherence on the whole homotopy category.
-/
theorem natTrans₄_ext_cofibrant (d : Data (C := C)) {F G : Ho ⥤ Ho ⥤ Ho ⥤ Ho ⥤ D}
    {τ τ' : F ⟶ G}
    (h : ∀ (X Y Z E : C) [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z] [IsCofibrant E],
      (((τ.app ((π).obj X)).app ((π).obj Y)).app ((π).obj Z)).app ((π).obj E) =
        (((τ'.app ((π).obj X)).app ((π).obj Y)).app ((π).obj Z)).app ((π).obj E)) : τ = τ' := by
  apply natTrans_ext_cofibrant d
  intro X _
  apply natTrans₃_ext_cofibrant d
  intro Y Z E _ _ _
  exact h X Y Z E

end HomotopicalAlgebra.GeneratedFunctorialReplacements

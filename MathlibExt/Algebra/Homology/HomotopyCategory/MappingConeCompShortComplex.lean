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

public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-!
# Mapping-cone composition and short-complex quotients

Composing the third morphism of a mapping-cone composition triangle with the
shift of the canonical cone-to-quotient map replaces the shifted cone
inclusion by the shifted quotient map.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated

universe v u

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- The mapping-cone composition connecting morphism, followed by the
canonical cone-to-quotient map of a short complex. -/
@[reassoc]
theorem mappingConeCompTriangle_mor₃_comp_descShortComplex_shift
    (S : ShortComplex (CochainComplex C ℤ))
    {X : CochainComplex C ℤ} (g : S.X₂ ⟶ X) :
    (CochainComplex.mappingConeCompTriangle S.f g).mor₃ ≫
        (descShortComplex S)⟦(1 : ℤ)⟧' =
      (triangle g).mor₃ ≫ S.g⟦(1 : ℤ)⟧' := by
  dsimp [CochainComplex.mappingConeCompTriangle]
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp,
    inr_descShortComplex]

end CochainComplex.mappingCone

end

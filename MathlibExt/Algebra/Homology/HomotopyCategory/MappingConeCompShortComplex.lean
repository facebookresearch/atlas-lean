/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-!
# Cone-composition boundaries and short-complex descendants

For a short complex `S : K → L → M` of integer cochains in an
abelian category and any `g : L → X`, composing the third map of
the cone composition triangle with the shifted descendant
`Cone(S.f)[1] → M[1]` gives the ordinary cone boundary for `g`
followed by `S.g[1]`. No exactness of the short complex is required.
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
/-- In an abelian category `C`, let `S : K → L → M` be a short
complex of integer cochains and `g : L → X`. The third map of
`mappingConeCompTriangle(S.f,g)`, followed by the descendant
`Cone(S.f) → M` shifted by one, equals the third map of the cone
triangle of `g` followed by `S.g[1]`. -/
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

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.FppfConstantSheafSection

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Exact-source consumer, with the original binders and universes. -/
theorem exactSource
    {E : Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}}
    (g : E ⟶ (constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj
      (.of (ULift.{1} ℤ)))
    (e : ToType (E.obj.obj (op (Spec (.of ℤ)))))
    (he : g.hom.app (op (Spec (.of ℤ))) e =
      (constantSheafAdj Scheme.fppfTopology.{0} AddCommGrpCat.{1}
          specZIsTerminal).unit.app (.of (ULift.{1} ℤ)) (ULift.up 1)) :
    ∃ s : (constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj
        (.of (ULift.{1} ℤ)) ⟶ E,
      s ≫ g = 𝟙 _ :=
  fppf_exists_section_of_map_eq_unit g e he

end AlgebraicGeometry

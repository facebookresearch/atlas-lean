/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.SmoothSectionsHenselian

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

-- `exactSource` consumer with the original binders.
example {R : Type u} [CommRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] :
    Dense {x : {x : T // t.base x = IsLocalRing.closedPoint R} |
      ∃ s : Spec (CommRingCat.of R) ⟶ T, s ≫ t = 𝟙 _ ∧
        s.base (IsLocalRing.closedPoint R) = x.1} :=
  AlgebraicGeometry.Smooth.dense_setOf_exists_section_of_henselianLocalRing_of_isAlgClosed t

-- Boundary: the identity over `Spec R` itself, whose every closed-fibre
-- point (there is one) admits the identity as a section, and the resulting
-- dense set is the whole closed fibre.
example {R : Type u} [CommRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] :
    Dense {x : {x : Spec (CommRingCat.of R) //
        (𝟙 (Spec (CommRingCat.of R)) : Spec (CommRingCat.of R) ⟶
          Spec (CommRingCat.of R)) x = IsLocalRing.closedPoint R} |
      ∃ s : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R),
        s ≫ 𝟙 (Spec (CommRingCat.of R)) = 𝟙 _ ∧
          s.base (IsLocalRing.closedPoint R) = x.1} :=
  AlgebraicGeometry.Smooth.dense_setOf_exists_section_of_henselianLocalRing_of_isAlgClosed
    (𝟙 (Spec (CommRingCat.of R)))

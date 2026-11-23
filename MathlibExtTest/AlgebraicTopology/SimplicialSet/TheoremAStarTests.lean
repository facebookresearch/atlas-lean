/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.TheoremAStar

/-!
# Simplicial product Theorem A* tests

The tests pin the all-degree left-fiber hypothesis, the source-first product
orientation, the intermediate simplex-resolution map, and the augmentation
square used by two-out-of-three.
-/

noncomputable section

open CategoryTheory Limits MorphismProperty Opposite Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.TheoremAStarTests

variable {X Y T : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ T)

variable (h : ∀ (m : ℕ) (y : Y _⦋m⦌),
  TopCat.weakHomotopyEquivalences
    (SSet.toTop.map (SSet.leftFiber.π f y ≫ g)))

/-- The product-induced map of simplex resolutions is weak. -/
example : SSet.realizationWeakEquivalences
    (SSet.simplexResolutionMap
      (p := f) (q := (prod.fst : Y ⨯ T ⟶ Y))
      (prod.lift f g) (prod.lift_fst f g)) :=
  SSet.simplexResolutionMap_prod_mem_realizationWeakEquivalences f g h

/-- The augmentation square is oriented from the direct resolution map to
the source augmentation followed by the ordered pair. -/
example :
    SSet.simplexResolutionMap
        (p := f) (q := (prod.fst : Y ⨯ T ⟶ Y))
        (prod.lift f g) (prod.lift_fst f g) ≫
      SSet.simplexResolutionAugmentation
        (prod.fst : Y ⨯ T ⟶ Y) =
    SSet.simplexResolutionAugmentation f ≫ prod.lift f g :=
  SSet.simplexResolutionAugmentation_naturality
    (p := f) (q := (prod.fst : Y ⨯ T ⟶ Y))
    (prod.lift f g) (prod.lift_fst f g)

/-- The public theorem concludes on the literal source-first pairing. -/
example : TopCat.weakHomotopyEquivalences
    (SSet.toTop.map (prod.lift f g)) :=
  SSet.theoremAStar f g h

/-- The equivalent realization-weak formulation is available through the
public comparison theorem. -/
example : SSet.realizationWeakEquivalences (prod.lift f g) :=
  show TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (prod.lift f g)) from
    SSet.theoremAStar f g h

section UniverseOne

variable {X1 Y1 T1 : SSet.{1}} (f1 : X1 ⟶ Y1) (g1 : X1 ⟶ T1)
variable (h1 : ∀ (m : ℕ) (y : Y1 _⦋m⦌),
  TopCat.weakHomotopyEquivalences
    (SSet.toTop.map (SSet.leftFiber.π f1 y ≫ g1)))

example : TopCat.weakHomotopyEquivalences
    (SSet.toTop.map (prod.lift f1 g1)) :=
  SSet.theoremAStar f1 g1 h1

end UniverseOne

end MathlibExtTest.AlgebraicTopology.SimplicialSet.TheoremAStarTests

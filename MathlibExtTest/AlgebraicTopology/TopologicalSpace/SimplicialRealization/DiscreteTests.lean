/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.Discrete

/-!
# Public clients for levelwise-discrete realization
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite Convexity

open scoped Simplicial

universe u

namespace SSet

variable (X Y : SSet.{u})

example : SSet.{u} ⥤ SimplicialObject TopCat.{u} :=
  levelwiseDiscrete

example : SSet.{u} ⥤ TopCat.{u} :=
  levelwiseDiscreteRealization

example :
    SSet.toTop.obj X ≅
      TopCat.simplicialRealization.obj (levelwiseDiscrete.obj X) :=
  toTopLevelwiseDiscreteNatIso.app X

example (f : X ⟶ Y) :
    SSet.toTop.map f ≫ (toTopLevelwiseDiscreteNatIso.app Y).hom =
      (toTopLevelwiseDiscreteNatIso.app X).hom ≫
        TopCat.simplicialRealization.map
          (Functor.whiskerRight f TopCat.discrete) :=
  toTopLevelwiseDiscreteNatIso_hom_naturality f

example : levelwiseDiscreteRealization ⊣ TopCat.toSSet :=
  levelwiseDiscreteRealizationAdj

example (n : SimplexCategory) (x : X.obj (op n))
    (s : StdSimplex ℝ (Fin (n.len + 1))) :
    TopCat.toSSetObjEquiv (levelwiseDiscreteRealization.obj X) (op n)
        ((levelwiseDiscreteRealizationUnit X).app (op n) x) s =
      TopCat.SimplicialRealization.ι (levelwiseDiscrete.obj X) n
        (x, topSimplexULiftHomeomorph n s) :=
  levelwiseDiscreteRealizationUnit_apply X n x s

example {Z : TopCat.{u}} (g : X ⟶ TopCat.toSSet.obj Z)
    (n : SimplexCategory) :
    TopCat.SimplicialRealization.ι (levelwiseDiscrete.obj X) n ≫
        levelwiseDiscreteRealizationDesc g =
      levelwiseDiscreteRealizationDescLeg g n :=
  levelwiseDiscreteRealization_ι_desc g n

example (Z : TopCat.{u}) :
    (levelwiseDiscreteRealization.obj X ⟶ Z) ≃
      (X ⟶ TopCat.toSSet.obj Z) :=
  levelwiseDiscreteRealizationHomEquiv X Z

example (Z : TopCat.{u}) (f : X ⟶ Y)
    (g : Y ⟶ TopCat.toSSet.obj Z) :
    (levelwiseDiscreteRealizationHomEquiv X Z).symm (f ≫ g) =
      levelwiseDiscreteRealization.map f ≫
        (levelwiseDiscreteRealizationHomEquiv Y Z).symm g :=
  levelwiseDiscreteRealizationHomEquiv_naturality_left_symm f g

example (Z W : TopCat.{u})
    (f : levelwiseDiscreteRealization.obj X ⟶ Z) (g : Z ⟶ W) :
    levelwiseDiscreteRealizationHomEquiv X W (f ≫ g) =
      levelwiseDiscreteRealizationHomEquiv X Z f ≫ TopCat.toSSet.map g :=
  levelwiseDiscreteRealizationHomEquiv_naturality_right f g

end SSet

end

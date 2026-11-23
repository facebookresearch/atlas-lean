/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.Homotopy

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Simplicial
open CategoryTheory.SimplicialObject.Augmented

open scoped Simplicial

universe u

namespace TopCat.SimplicialRealization.HomotopyTests

variable {X Y Z : SimplicialObject TopCat.{u}} {f g : X ⟶ Y}

example (H : SimplicialObject.Homotopy f g) :
    ContinuousMap.Homotopy
      (TopCat.simplicialRealization.map f).hom
      (TopCat.simplicialRealization.map g).hom :=
  realizationHomotopy H

example (H : SimplicialObject.Homotopy f g)
    (x : TopCat.simplicialRealization.obj X) :
    realizationHomotopy H (0, x) = TopCat.simplicialRealization.map f x :=
  (realizationHomotopy H).map_zero_left x

example (H : SimplicialObject.Homotopy f g)
    (x : TopCat.simplicialRealization.obj X) :
    realizationHomotopy H (1, x) = TopCat.simplicialRealization.map g x :=
  (realizationHomotopy H).map_one_left x

example (H : SimplicialObject.Homotopy f g) :
    (H.h (Fin.last 0) ≫ Y.δ (Fin.last 1) =
        f.app (Opposite.op (SimplexCategory.mk 0))) ∧
      (H.h (0 : Fin 1) ≫ Y.δ 0 =
        g.app (Opposite.op (SimplexCategory.mk 0))) :=
  ⟨H.h_last_comp_δ_last 0, H.h_zero_comp_δ_zero 0⟩

example (H : SimplicialObject.Homotopy f g) :
    (H.h (Fin.last 1) ≫ Y.δ (Fin.last 2) =
        f.app (Opposite.op (SimplexCategory.mk 1))) ∧
      (H.h (0 : Fin 2) ≫ Y.δ 0 =
        g.app (Opposite.op (SimplexCategory.mk 1))) :=
  ⟨H.h_last_comp_δ_last 1, H.h_zero_comp_δ_zero 1⟩

example (f : X ⟶ Y) :
    ContinuousMap.Homotopy
      (TopCat.simplicialRealization.map f).hom
      (TopCat.simplicialRealization.map f).hom :=
  realizationHomotopy (SimplicialObject.Homotopy.refl f)

example (X : SimplicialObject TopCat.{u}) :
    TopCat.simplicialRealization.obj (SimplicialObject.opFunctor.obj X) ≅
      TopCat.simplicialRealization.obj X :=
  opIso X

example (X : SimplicialObject TopCat.{u}) (n : SimplexCategory)
    (x : (SimplicialObject.opFunctor.obj X).obj (op n) ×
      SimplexCategory.toTop.{u}.obj n) :
    (ι (SimplicialObject.opFunctor.obj X) n ≫ (opIso X).hom) x =
      ι X n
        ((SimplicialObject.opObjIso (X := X) (n := op n)).hom.hom x.1,
          ULift.up (Convexity.StdSimplex.map
            (Fin.rev : Fin (n.len + 1) → Fin (n.len + 1)) x.2.down)) :=
  opIso_ι_apply X n x

example (f : X ⟶ Y) :
    TopCat.simplicialRealization.map (SimplicialObject.opFunctor.map f) ≫
        (opIso Y).hom =
      (opIso X).hom ≫ TopCat.simplicialRealization.map f :=
  opIso_naturality f

example (X : SimplicialObject TopCat.{u}) :
    (opIso (SimplicialObject.opFunctor.obj X)).hom ≫ (opIso X).hom =
      TopCat.simplicialRealization.map
        (SimplicialObject.opFunctorCompOpFunctorIso.hom.app X) :=
  opIso_double X

example (X : SimplicialObject TopCat.{u}) :
    (opIso X).hom ≫ (opIso X).inv = 𝟙 _ := by simp

example (Q : TopCat.{u}) :
    TopCat.simplicialRealization.map
        ((SimplicialObject.constCompOpFunctorIso (C := TopCat.{u})).hom.app Q) ≫
        (constIso Q).hom =
      (opIso ((SimplicialObject.const TopCat).obj Q)).hom ≫
        (constIso Q).hom :=
  opIso_constIso Q

example {A : SimplicialObject.Augmented TopCat.{u}}
    (ed : A.ExtraDegeneracy) :
    ContinuousMap.HomotopyEquiv
      (TopCat.simplicialRealization.obj A.left) A.right :=
  ed.realizationHomotopyEquiv

example {A : SimplicialObject.Augmented TopCat.{u}}
    (ed : A.ExtraDegeneracy) :
    ed.realizationHomotopyEquiv.toFun =
      (TopCat.simplicialRealization.map A.hom ≫
        (constIso A.right).hom).hom :=
  rfl

example {A : SimplicialObject.Augmented TopCat.{u}}
    (ed : A.RightExtraDegeneracy) :
    ContinuousMap.HomotopyEquiv
      (TopCat.simplicialRealization.obj A.left) A.right :=
  ed.realizationHomotopyEquiv

example {A : SimplicialObject.Augmented TopCat.{u}}
    (ed : A.RightExtraDegeneracy) :
    ed.realizationHomotopyEquiv.toFun =
      (TopCat.simplicialRealization.map A.hom ≫
        (constIso A.right).hom).hom :=
  RightExtraDegeneracy.realizationHomotopyEquiv_toFun ed

section UniverseOne

example (X : SimplicialObject TopCat.{1}) :
    TopCat.simplicialRealization.obj (SimplicialObject.opFunctor.obj X) ≅
      TopCat.simplicialRealization.obj X :=
  opIso X

example {A : SimplicialObject.Augmented TopCat.{1}}
    (ed : A.RightExtraDegeneracy) :
    ed.realizationHomotopyEquiv.toFun =
      (TopCat.simplicialRealization.map A.hom ≫
        (constIso A.right).hom).hom := by
  apply RightExtraDegeneracy.realizationHomotopyEquiv_toFun

end UniverseOne

section UniverseZero

example (X : SimplicialObject TopCat.{0}) :
    TopCat.simplicialRealization.obj (SimplicialObject.opFunctor.obj X) ≅
      TopCat.simplicialRealization.obj X :=
  opIso X

example {A : SimplicialObject.Augmented TopCat.{0}}
    (ed : A.ExtraDegeneracy) :
    ed.realizationHomotopyEquiv.toFun =
      (TopCat.simplicialRealization.map A.hom ≫
        (constIso A.right).hom).hom :=
  rfl

end UniverseZero

#print axioms realizationHomotopy
#print axioms opIso
#print axioms opIso_naturality
#print axioms opIso_double
#print axioms
  CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy.realizationHomotopyEquiv
#print axioms
  CategoryTheory.SimplicialObject.Augmented.RightExtraDegeneracy.realizationHomotopyEquiv

end TopCat.SimplicialRealization.HomotopyTests

end

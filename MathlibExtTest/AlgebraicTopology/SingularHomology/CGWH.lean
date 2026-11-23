/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularHomology.CGWH

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits

universe a w v u

#check @CGWH.singularChainComplexFunctor
#check @CGWH.singularHomologyFunctor
#check @CGWH.singularChainIntFunctor
#check @CGWH.singularHomologyIntFunctor
#check @CGWH.reducedSingularHomologyFunctor
#check @CGWH.singularIntegralChainFunctor
#check @CGWH.singularIntegralHomologyFunctor
#check @CGWH.singularChainComplexFunctor_obj
#check @CGWH.singularChainComplexFunctor_map
#check @CGWH.singularHomologyFunctor_obj
#check @CGWH.singularHomologyFunctor_map
#check @CGWH.singularChainIntFunctor_obj
#check @CGWH.singularChainIntFunctor_map
#check @CGWH.singularHomologyIntFunctor_obj
#check @CGWH.singularHomologyIntFunctor_map
#check @CGWH.reducedSingularHomologyFunctor_obj
#check @CGWH.reducedSingularHomologyFunctor_map
#check @CGWH.singularHomologyPointZeroIso
#check @CGWH.isZero_singularHomologyPoint_of_ne_zero
#check @CGWH.singularHomologyIntPointZeroIso
#check @CGWH.isZero_singularHomologyIntPoint_of_ne_zero
#check @CGWH.isZero_reducedSingularHomologyPoint
#check @CGWH.weakHomotopyEquivalences.quasiIso_singularChainComplexMap
#check @CGWH.weakHomotopyEquivalences.isIso_singularHomologyFunctor_map
#check @CGWH.weakHomotopyEquivalences.isIso_reducedSingularHomologyFunctor_map

section Generic

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C] [CategoryWithHomology C]
variable (A : C) {X Y : CGWH.{a, w}} (f : X ⟶ Y)

example : CGWH.{a, w} ⥤ ChainComplex C ℕ :=
  CGWH.singularChainComplexFunctor C A

example (n : ℕ) : CGWH.{a, w} ⥤ C :=
  CGWH.singularHomologyFunctor C A n

example :
    (CGWH.singularChainComplexFunctor C A).obj X =
      ((AlgebraicTopology.singularChainComplexFunctor C).obj A).obj
        (CGWH.cgwhToTop.obj X) :=
  rfl

example :
    (CGWH.singularChainComplexFunctor C A).map f =
      ((AlgebraicTopology.singularChainComplexFunctor C).obj A).map
        (CGWH.cgwhToTop.map f) :=
  rfl

example (n : ℕ) :
    (CGWH.singularHomologyFunctor C A n).obj X =
      ((AlgebraicTopology.singularHomologyFunctor C n).obj A).obj
        (CGWH.cgwhToTop.obj X) :=
  rfl

example (n : ℕ) :
    (CGWH.singularHomologyFunctor C A n).map f =
      ((AlgebraicTopology.singularHomologyFunctor C n).obj A).map
        (CGWH.cgwhToTop.map f) :=
  rfl

end Generic

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{w} C]
variable (A : C) {X Y : CGWH.{a, w}} (f : X ⟶ Y)

example : CGWH.{a, w} ⥤ ChainComplex C ℤ :=
  CGWH.singularChainIntFunctor C A

example (z : ℤ) : CGWH.{a, w} ⥤ C :=
  CGWH.singularHomologyIntFunctor C A z

example (n : ℕ) : CGWH.{a, w} ⥤ C :=
  CGWH.reducedSingularHomologyFunctor C A n

example :
    (CGWH.singularChainIntFunctor C A).obj X =
      (AlgebraicTopology.singularChainIntFunctor C A).obj
        (CGWH.cgwhToTop.obj X) :=
  rfl

example :
    (CGWH.singularChainIntFunctor C A).map f =
      (AlgebraicTopology.singularChainIntFunctor C A).map
        (CGWH.cgwhToTop.map f) :=
  rfl

example (z : ℤ) :
    (CGWH.singularHomologyIntFunctor C A z).obj X =
      (AlgebraicTopology.singularHomologyIntFunctor C A z).obj
        (CGWH.cgwhToTop.obj X) :=
  rfl

example (z : ℤ) :
    (CGWH.singularHomologyIntFunctor C A z).map f =
      (AlgebraicTopology.singularHomologyIntFunctor C A z).map
        (CGWH.cgwhToTop.map f) :=
  rfl

example (n : ℕ) :
    (CGWH.reducedSingularHomologyFunctor C A n).obj X =
      (AlgebraicTopology.reducedSingularHomologyFunctor C A n).obj
        (CGWH.cgwhToTop.obj X) :=
  rfl

example (n : ℕ) :
    (CGWH.reducedSingularHomologyFunctor C A n).map f =
      (AlgebraicTopology.reducedSingularHomologyFunctor C A n).map
        (CGWH.cgwhToTop.map f) :=
  rfl

end Abelian

section Integral

variable {X Y : CGWH.{a, u}} (f : X ⟶ Y)

example : CGWH.{a, u} ⥤ ChainComplex AddCommGrpCat.{u} ℕ :=
  CGWH.singularIntegralChainFunctor

example (n : ℕ) : CGWH.{a, u} ⥤ AddCommGrpCat.{u} :=
  CGWH.singularIntegralHomologyFunctor n

example :
    CGWH.singularIntegralChainFunctor.obj X =
      AlgebraicTopology.singularIntegralChainFunctor.obj
        (CGWH.cgwhToTop.obj X) :=
  rfl

example :
    CGWH.singularIntegralChainFunctor.map f =
      AlgebraicTopology.singularIntegralChainFunctor.map
        (CGWH.cgwhToTop.map f) :=
  rfl

example (n : ℕ) :
    (CGWH.singularIntegralHomologyFunctor n).obj X =
      (AlgebraicTopology.singularIntegralHomologyFunctor n).obj
        (CGWH.cgwhToTop.obj X) :=
  rfl

example (n : ℕ) :
    (CGWH.singularIntegralHomologyFunctor n).map f =
      (AlgebraicTopology.singularIntegralHomologyFunctor n).map
        (CGWH.cgwhToTop.map f) :=
  rfl

end Integral

section Point

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{w} C]
variable (A : C)

example :
    (CGWH.singularHomologyFunctor C A 0).obj
        CGWH.point.{a, w} ≅ A :=
  CGWH.singularHomologyPointZeroIso.{a, w, v, u} C A

example :
    IsZero
      ((CGWH.singularHomologyFunctor C A 1).obj
        CGWH.point.{a, w}) :=
  CGWH.isZero_singularHomologyPoint_of_ne_zero.{a, w, v, u}
    C A 1 (by omega)

example :
    (CGWH.singularHomologyIntFunctor C A (0 : ℤ)).obj
        CGWH.point.{a, w} ≅ A :=
  CGWH.singularHomologyIntPointZeroIso.{a, w, v, u} C A

example :
    IsZero
      ((CGWH.singularHomologyIntFunctor C A (-1 : ℤ)).obj
        CGWH.point.{a, w}) :=
  CGWH.isZero_singularHomologyIntPoint_of_ne_zero.{a, w, v, u}
    C A (-1) (by omega)

example (n : ℕ) :
    IsZero
      ((CGWH.reducedSingularHomologyFunctor C A n).obj
        CGWH.point.{a, w}) :=
  CGWH.isZero_reducedSingularHomologyPoint.{a, w, v, u} C A n

example :
    IsZero
      ((CGWH.reducedSingularHomologyFunctor C A 0).obj
        CGWH.point.{a, w}) :=
  CGWH.isZero_reducedSingularHomologyPoint.{a, w, v, u} C A 0

example :
    IsZero
      ((CGWH.reducedSingularHomologyFunctor C A 1).obj
        CGWH.point.{a, w}) :=
  CGWH.isZero_reducedSingularHomologyPoint.{a, w, v, u} C A 1

end Point

section Weak

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C] [CategoryWithHomology C]
variable {X Y : CGWH.{a, w}} {f : X ⟶ Y}
variable (hf : CGWH.weakHomotopyEquivalences f) (A : C)

example : QuasiIso ((CGWH.singularChainComplexFunctor C A).map f) :=
  CGWH.weakHomotopyEquivalences.quasiIso_singularChainComplexMap.{a, w, v, u}
    hf A

example (n : ℕ) : IsIso ((CGWH.singularHomologyFunctor C A n).map f) :=
  CGWH.weakHomotopyEquivalences.isIso_singularHomologyFunctor_map.{a, w, v, u}
    hf A n

example : IsIso ((CGWH.singularHomologyFunctor C A 0).map f) :=
  CGWH.weakHomotopyEquivalences.isIso_singularHomologyFunctor_map.{a, w, v, u}
    hf A 0

example (n : ℕ) :
    IsIso ((CGWH.singularHomologyFunctor C A (n + 1)).map f) :=
  CGWH.weakHomotopyEquivalences.isIso_singularHomologyFunctor_map.{a, w, v, u}
    hf A (n + 1)

end Weak

section WeakReduced

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{w} C]
variable {X Y : CGWH.{a, w}} {f : X ⟶ Y}
variable (hf : CGWH.weakHomotopyEquivalences f) (A : C)

example (n : ℕ) :
    IsIso ((CGWH.reducedSingularHomologyFunctor C A n).map f) :=
  CGWH.weakHomotopyEquivalences.isIso_reducedSingularHomologyFunctor_map.{a, w, v, u}
    hf A n

example :
    IsIso ((CGWH.reducedSingularHomologyFunctor C A 0).map f) :=
  CGWH.weakHomotopyEquivalences.isIso_reducedSingularHomologyFunctor_map.{a, w, v, u}
    hf A 0

example (n : ℕ) :
    IsIso ((CGWH.reducedSingularHomologyFunctor C A (n + 1)).map f) :=
  CGWH.weakHomotopyEquivalences.isIso_reducedSingularHomologyFunctor_map.{a, w, v, u}
    hf A (n + 1)

end WeakReduced

section WeakIntegral

variable {X Y : CGWH.{a, u}} {f : X ⟶ Y}
variable (hf : CGWH.weakHomotopyEquivalences f)

example : QuasiIso (CGWH.singularIntegralChainFunctor.map f) :=
  CGWH.weakHomotopyEquivalences.quasiIso_singularChainComplexMap.{a, u, u, u + 1}
    hf AlgebraicTopology.singularIntegralCoefficients

example (n : ℕ) :
    IsIso ((CGWH.singularIntegralHomologyFunctor n).map f) :=
  CGWH.weakHomotopyEquivalences.isIso_singularHomologyFunctor_map.{a, u, u, u + 1}
    hf AlgebraicTopology.singularIntegralCoefficients n

end WeakIntegral

end

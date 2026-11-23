/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatHomology

/-!
# Homology with local coefficients on a CGWH space

This file is the thin CGWH wrapper around local-coefficient homology on the
underlying TopCat object.  The compact-probe universe does not enter the
coefficient target.  Constant local coefficients compare to the existing
singular homology object of the underlying topological space.

No map of base spaces, local-coefficient-equivalence predicate, acyclicity,
or plus construction is introduced.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe uR uK uX

namespace CGWH

namespace LocalSystem

variable {R : Type uR} [CommRing R] {X : CGWH.{uK, uX}}
variable {L K P : CGWH.LocalSystem R X}

/-- Whisker a natural transformation of CGWH local systems by the singular
fundamental-groupoid functor of the underlying TopCat object. -/
noncomputable abbrev toSingularMap (alpha : L ⟶ K) :
    L.toSingular ⟶ K.toSingular :=
  TopCat.LocalSystem.toSingularMap alpha

@[simp]
theorem toSingularMap_app (alpha : L ⟶ K)
    (x : SSet.FundamentalGroupoid
      (TopCat.toSSet.obj X.toTop)) :
    (toSingularMap alpha).app x =
      alpha.app ((TopCat.singularFundamentalGroupoidFunctor
        X.toTop).obj x) :=
  rfl

@[simp]
theorem toSingularMap_id :
    toSingularMap (𝟙 L) = 𝟙 L.toSingular :=
  TopCat.LocalSystem.toSingularMap_id

@[simp]
theorem toSingularMap_comp (alpha : L ⟶ K) (beta : K ⟶ P) :
    toSingularMap (alpha ≫ beta) =
      toSingularMap alpha ≫ toSingularMap beta :=
  TopCat.LocalSystem.toSingularMap_comp alpha beta

end LocalSystem

section Homology

variable {R : Type uR} [CommRing R] {X : CGWH.{uK, uX}}
variable {L K P : CGWH.LocalSystem R X}

/-- Homology in degree `n` of the local-coefficient chain complex on the
underlying topological space. -/
noncomputable abbrev localCoefficientHomology
    (L : CGWH.LocalSystem R X) (n : ℕ) :
    ModuleCat.{max uR uX} R :=
  TopCat.localCoefficientHomology L n

/-- The homology map induced by a natural transformation of CGWH local
systems. -/
noncomputable abbrev localCoefficientHomologyMap
    (alpha : L ⟶ K) (n : ℕ) :
    localCoefficientHomology L n ⟶
      localCoefficientHomology K n :=
  TopCat.localCoefficientHomologyMap alpha n

@[simp]
theorem localCoefficientHomologyMap_id (n : ℕ) :
    localCoefficientHomologyMap (𝟙 L) n = 𝟙 _ :=
  TopCat.localCoefficientHomologyMap_id n

@[reassoc]
theorem localCoefficientHomologyMap_comp
    (alpha : L ⟶ K) (beta : K ⟶ P) (n : ℕ) :
    localCoefficientHomologyMap (alpha ≫ beta) n =
      localCoefficientHomologyMap alpha n ≫
        localCoefficientHomologyMap beta n :=
  TopCat.localCoefficientHomologyMap_comp alpha beta n

/-- CGWH local-coefficient homology in degree `n` as a functor of the local
system on one fixed space. -/
noncomputable abbrev localCoefficientHomologyFunctor (n : ℕ) :
    CGWH.LocalSystem R X ⥤ ModuleCat.{max uR uX} R :=
  TopCat.localCoefficientHomologyFunctor (X := X.toTop) n

@[simp]
theorem localCoefficientHomologyFunctor_obj
    (L : CGWH.LocalSystem R X) (n : ℕ) :
    (localCoefficientHomologyFunctor n).obj L =
      localCoefficientHomology L n :=
  rfl

@[simp]
theorem localCoefficientHomologyFunctor_map
    (alpha : L ⟶ K) (n : ℕ) :
    (localCoefficientHomologyFunctor n).map alpha =
      localCoefficientHomologyMap alpha n :=
  rfl

end Homology

section Constant

variable {R : Type uR} [CommRing R] {X : CGWH.{uK, uX}}

/-- Native constant local-coefficient homology agrees with ordinary singular
homology of the underlying topological space. -/
noncomputable abbrev constantLocalCoefficientHomologyIso
    (M : ModuleCat.{max uR uX} R) (n : ℕ) :
    localCoefficientHomology
        (CGWH.constantLocalSystem (X := X) M) n ≅
      ((AlgebraicTopology.singularHomologyFunctor
        (ModuleCat.{max uR uX} R) n).obj M).obj X.toTop :=
  TopCat.constantLocalCoefficientHomologyIso
    (X := X.toTop) M n

@[simp]
theorem constantLocalCoefficientHomologyIso_hom
    (M : ModuleCat.{max uR uX} R) (n : ℕ) :
    (constantLocalCoefficientHomologyIso (X := X) M n).hom =
      HomologicalComplex.homologyMap
        (CGWH.constantLocalCoefficientChainIso (X := X) M).hom n :=
  rfl

@[simp]
theorem constantLocalCoefficientHomologyIso_inv
    (M : ModuleCat.{max uR uX} R) (n : ℕ) :
    (constantLocalCoefficientHomologyIso (X := X) M n).inv =
      HomologicalComplex.homologyMap
        (CGWH.constantLocalCoefficientChainIso (X := X) M).inv n :=
  rfl

end Constant

end CGWH

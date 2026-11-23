/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.NativeCoverBarAugmentation
import MathlibExt.AlgebraicTopology.SingularHomology.Integral

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

/-- The coefficient diagram uses the original endomorphism group and deck map. -/
example (X : SSet.{u}) (x : X _⦋0⦌)
    (g : End (SSet.FundamentalGroupoid.mk x)) :
    (SSet.KanComplex.nativeCoverDeckFunctor X x).map
        (X := SingleObj.star (End (SSet.FundamentalGroupoid.mk x)))
        (Y := SingleObj.star (End (SSet.FundamentalGroupoid.mk x))) g =
      SSet.KanComplex.nativeCoverDeckMap g :=
  SSet.KanComplex.nativeCoverDeckFunctor_map X x g

/-- The actual original scalar projection is an equivalence; the original
base is explicitly connected as well as Kan. -/
example (X : SSet.{u}) [SSet.KanComplex X] [X.IsConnected] (x : X _⦋0⦌) :
    (SSet.BousfieldKanRowsOf.rowProjection.{0, u, 0}
      (SSet.KanComplex.nativeCoverProjectionCocone X x) (op ⦋2⦌)).IsEquivalence :=
  SSet.KanComplex.nativeCoverRowProjection_isEquivalence X x (op ⦋2⦌)

/-- The same original augmentation has the original base as its target. -/
example (X : SSet.{u}) [SSet.KanComplex X] [X.IsConnected] (x : X _⦋0⦌) :
    SSet.realizationWeakEquivalences (SSet.KanComplex.nativeCoverBarAugmentation X x) :=
  SSet.KanComplex.nativeCoverBarAugmentation_mem_realizationWeakEquivalences X x

/-- An original weighted cover simplex augments to its original projected
simplex, with no replacement of the base or the coefficient. -/
example (X : SSet.{u}) (x : X _⦋0⦌) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx
      (SingleObj (End (SSet.FundamentalGroupoid.mk x)))
      (CategoryBar.replUnit (SingleObj (End (SSet.FundamentalGroupoid.mk x)))) n)
    (s : (SSet.KanComplex.nativeCover X x) _⦋n⦌) :
    (SSet.KanComplex.nativeCoverBarAugmentation X x).app (op ⦋n⦌)
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit (SingleObj (End (SSet.FundamentalGroupoid.mk x))))
          (SSet.KanComplex.nativeCoverDeckFunctor X x) n p).app (op ⦋n⦌) s) =
      (SSet.KanComplex.nativeCoverProjection X x).app (op ⦋n⦌) s :=
  ConcreteCategory.congr_hom (SSet.KanComplex.nativeCoverBarAugmentation_weighted X x n p) s

/-- The actual signed total returns the original integral chains, without a
vanishing premise on any cover homology group. -/
example (X : SSet.{u}) [SSet.KanComplex X] [X.IsConnected] (x : X _⦋0⦌) :
    QuasiIso (SSet.KanComplex.nativeCoverTotalAugmentation AddCommGrpCat.{u}
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) X x) :=
  SSet.KanComplex.nativeCoverTotalAugmentation_quasiIso_addCommGrp _ X x

/-- Literal large-universe integral module coefficients retain the original
base's H2 as the total homology target. -/
example (X : SSet.{u}) [SSet.KanComplex X] [X.IsConnected] (x : X _⦋0⦌) :
    (SSet.bkAlternatingTotalComplex (ModuleCat.{u} (ULift.{u} ℤ))
      (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ))
      (SSet.KanComplex.nativeCoverDeckFunctor X x)).homology 2 ≅
        X.homology (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ)) 2 :=
  SSet.KanComplex.nativeCoverTotalHomologyIso _ X x 2

end

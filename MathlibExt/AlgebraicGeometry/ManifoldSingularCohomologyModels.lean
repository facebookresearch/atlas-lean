/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Actual singular cochains and rational cohomology on manifolds

Chains are the native singular-set/free-module alternating chain complex.
Cochains are its actual linear dual, degree by degree, with the native
opposite-complex differential. Cohomology is the native homology of that
cochain complex. No cohomology carrier or characteristic class is supplied
as an unrelated parameter.

Native source: Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679,
SingularHomology/Basic.lean (Andrew Yang), Linear/Yoneda.lean and
Algebra/Homology/Opposite.lean, Apache 2.0.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ManifoldSingularCohomologyModels

open CategoryTheory Opposite AlgebraicTopology

variable (R : Type) [CommRing R]

/-- The actual native singular chains with coefficient R. -/
def singularChains (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} R) ℕ :=
  (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} R)).obj
    (ModuleCat.of R R))).obj X

/-- The actual contravariant native linear dual on every chain term. -/
def coefficientDual : (ModuleCat.{0} R)ᵒᵖ ⥤ ModuleCat.{0} R :=
  (linearYoneda R (ModuleCat.{0} R)).obj (ModuleCat.of R R)

instance : (coefficientDual R).Additive :=
  inferInstanceAs (((linearYoneda R (ModuleCat.{0} R)).obj (ModuleCat.of R R)).Additive)

/-- The full native singular cochain complex, with no finite-support restriction on cochains. -/
def singularCochains (X : TopCat.{0}) : CochainComplex (ModuleCat.{0} R) ℕ :=
  ((coefficientDual R).mapHomologicalComplex (.up ℕ)).obj
    ((HomologicalComplex.opFunctor (ModuleCat.{0} R) (.down ℕ)).obj (op (singularChains R X)))

/-- Actual continuous-map pullback is the native dual of the map on singular chains. -/
def singularCochainsMap {X Y : TopCat.{0}} (f : X ⟶ Y) :
    singularCochains R Y ⟶ singularCochains R X :=
  ((coefficientDual R).mapHomologicalComplex (.up ℕ)).map
    ((HomologicalComplex.opFunctor (ModuleCat.{0} R) (.down ℕ)).map
      ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} R)).obj
        (ModuleCat.of R R))).map f).op)

/-- Rational cohomology is actual singular cochain cohomology, in every degree. -/
def rationalCohomology (X : TopCat.{0}) (p : ℕ) : ModuleCat.{0} ℚ :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (.up ℕ) p).obj (singularCochains ℚ X)

/-- Real singular cohomology uses the same actual chain/cochain model. -/
def realCohomology (X : TopCat.{0}) (p : ℕ) : ModuleCat.{0} ℝ :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℝ) (.up ℕ) p).obj (singularCochains ℝ X)

/-- The actual induced map on rational cohomology. -/
def rationalCohomologyMap {X Y : TopCat.{0}} (f : X ⟶ Y) (p : ℕ) :
    rationalCohomology Y p ⟶ rationalCohomology X p :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (.up ℕ) p).map
    (singularCochainsMap ℚ f)

end MathlibExt.AlgebraicGeometry.ManifoldSingularCohomologyModels

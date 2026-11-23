/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import MathlibExt.AlgebraicGeometry.AnalyticRealization

/-!
# The actual coherent analytic hypercohomology comparison

For the normalized analytic-to-algebraic map, use its actual module pullback
and the isomorphism identifying the pullback of the structure module with
the holomorphic structure module. Assuming exactness of this specified
pullback, Mathlib supplies the functor on derived categories. Hypercohomology
is `Hom(𝒪, K[n])`; the comparison is that functor's map, with its actual
unit and shift isomorphisms. No independent cohomology carrier or comparison
map is chosen here.

The exactness and geometric GAGA theorems remain requests in WantedExt.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CoherentAnalyticHypercohomology

open CategoryTheory CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry.AnalyticRealization

attribute [local instance] HasDerivedCategory.standard

variable (X : ComplexScheme) (d : ℕ) [AnalyticManifold X d]
  [RegularFunctions X d]

/-- Pullback of analytic modules has its already constructed left adjunction. -/
instance pullback_isLeftAdjoint : (pullback X d).IsLeftAdjoint :=
  (pullbackPushforwardAdjunction X d).isLeftAdjoint

/-- The actual pullback preserves colimits by its defining adjunction. -/
instance pullback_preservesFiniteColimits :
    PreservesFiniteColimits (pullback X d) := by infer_instance

/-- The canonical identification of the pulled-back structure module. -/
def pullbackUnitIso :
    (pullback X d).obj (SheafOfModules.unit X.left.ringCatSheaf) ≅
      SheafOfModules.unit (holomorphicRingSheaf X d) :=
  letI : (TopologicalSpace.Opens.map (pointMap X)).Final := inferInstance
  @asIso _ _ _ _
    (SheafOfModules.pullbackObjUnitToUnit.{0, 0, 0, 0, 0}
      (F := TopologicalSpace.Opens.map (pointMap X)) (ringMap X d))
    (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal
      (F := TopologicalSpace.Opens.map (pointMap X)) (ringMap X d))

variable [PreservesFiniteLimits (pullback X d)]

/-- Exactness of this specified pullback entails additivity. -/
instance pullback_additive : (pullback X d).Additive :=
  leftExactFunctor_le_additiveFunctor _ _ _
    ((leftExactFunctor_iff _).2 inferInstance)

/-- The actual exact analytic pullback on derived categories. -/
abbrev derivedPullback :
    DerivedCategory X.left.Modules ⥤ DerivedCategory (AnalyticModules X d) :=
  (pullback X d).mapDerivedCategory

/-- The algebraic structure module in cohomological degree zero. -/
abbrev algebraicUnit : DerivedCategory X.left.Modules :=
  (DerivedCategory.singleFunctor _ 0).obj
    (SheafOfModules.unit X.left.ringCatSheaf)

/-- The holomorphic structure module in cohomological degree zero. -/
abbrev analyticUnit : DerivedCategory (AnalyticModules X d) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (SheafOfModules.unit (holomorphicRingSheaf X d))

/-- The unit comparison is fixed by module pullback and its defining mate. -/
def derivedUnitIso :
    (derivedPullback X d).obj (algebraicUnit X) ≅ analyticUnit X d :=
  ((pullback X d).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (pullbackUnitIso X d)

/-- Algebraic hypercohomology, realized as actual derived morphisms. -/
abbrev AlgebraicHypercohomology (K : CochainComplex X.left.Modules ℤ) (n : ℤ) :=
  algebraicUnit X ⟶ (DerivedCategory.Q.obj K)⟦n⟧

/-- Analytic hypercohomology of the specified pullback complex. -/
abbrev AnalyticHypercohomology (K : CochainComplex X.left.Modules ℤ) (n : ℤ) :=
  analyticUnit X d ⟶
    ((derivedPullback X d).obj (DerivedCategory.Q.obj K))⟦n⟧

/-- The canonical hypercohomology comparison, with unit and shift normalized. -/
def comparison (K : CochainComplex X.left.Modules ℤ) (n : ℤ)
    (a : AlgebraicHypercohomology X K n) :
    AnalyticHypercohomology X d K n :=
  (derivedUnitIso X d).inv ≫ (derivedPullback X d).map a ≫
    ((derivedPullback X d).commShiftIso n).hom.app (DerivedCategory.Q.obj K)

/-- Its additivity is inherited from the actual derived functor. -/
theorem comparison_add (K : CochainComplex X.left.Modules ℤ) (n : ℤ)
    (a b : AlgebraicHypercohomology X K n) :
    comparison X d K n (a + b) =
      comparison X d K n a + comparison X d K n b := by
  simp [comparison, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

end MathlibExt.AlgebraicGeometry.CoherentAnalyticHypercohomology

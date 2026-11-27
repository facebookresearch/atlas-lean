/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Condensed.FrobeniusModuleHomModels
public import MathlibExt.CategoryTheory.DGSource.DGYoneda

/-!
# The actual Frobenius coefficient unit

The geometric unit comparison is forced by the native derived-extension
counit on the degree-zero coefficient sheaf and by the ordinary
extension/restriction mate. A compact unit arrow is normalized against
this comparison. Its Yoneda arrow under the full scalar-extension Hom
adjunction fixes the actual linearization before almost localization.

The almost-local phi unit retains the actual localization map and its
linearization square modulo a native DG boundary. No freely selected
rank-one Frobenius module is substituted for the coefficient unit.

Source: Mann, arXiv:2206.02022v1, Definitions 3.9.10 and 3.9.21.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.Condensed.FrobeniusCoefficientUnit

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.SemilinearDGModuleRestrictions
open MathlibExt.AlgebraicGeometry.AffineUntiltingGeometry
open LocalSolidCoefficientModels SolidTorsionFrobeniusModels SolidWeakPerfectModels
open GeometricScalarRestriction SolidAnalyticModules GeometricTopologicalRestriction
open TopologicalRings
open FrobeniusModuleHomModels CochainComplex.HomComplex

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime] (P : AffineUntilting p)
  (π : Pseudouniformizer p P) (h : π.element ∣ (p : P.pair.plus))
  (M : TorsionModel p P π) (F : FrobeniusModel p P π h M)

/-- The source-forced geometric Frobenius unit map, before analytic reflection. -/
def geometricUnitMap
    (E : ShiftedExtensionModel (coefficientFrobenius p P π h)
      (continuous_coefficientFrobenius p P π h)) :
    (E.functor _ _).obj (unitObject (TorsionRing p P π)) ⟶
      unitObject (TorsionRing p P π) := by
  letI := E.adjoint
  letI := E.derived
  let φ := coefficientFrobenius p P π h
  let hc := continuous_coefficientFrobenius p P π h
  let U := SheafOfModules.unit (ringSheaf (TorsionRing p P π))
  let S := CochainComplex.singleFunctor (GeometricModules (TorsionRing p P π)) 0
  exact (derivedExtensionCounit φ hc).app (S.obj U) ≫
    DerivedCategory.Q.map
      (((HomologicalComplex.singleMapHomologicalComplex
        (extension φ hc) (ComplexShape.up ℤ) 0).hom.app U)) ≫
    DerivedCategory.Q.map (S.map (unitExtension φ hc))

/-- The actual pre-almost coefficient representable, retaining its full module action. -/
abbrev unitRepresentable (U : UnitInductionModel p P π M) :
    RightModule (TorsionRing p P π) M.compact.objects :=
  ⟨dgRepresentable (TorsionRing p P π) U.val.unit⟩

/-- The coefficient representable is cofibrant, as every representable right DG module is
(`DGQuasiFunctorModels.isCofibrantModule_dgRepresentable`). -/
theorem unitRepresentable_cofibrant (U : UnitInductionModel p P π M) :
    IsCofibrantModule (unitRepresentable p P π M U) :=
  isCofibrantModule_dgRepresentable U.val.unit

set_option maxHeartbeats 1200000 in
/-- Compact Frobenius unit data is locked to the native geometric coefficient map: its arrow is
normalized against the bundled geometric normalization, using that normalization's derived
extension and its comparison isomorphism at the coefficient unit. -/
structure CompactUnit (U : UnitInductionModel p P π M) where
  /-- The geometric Frobenius normalization the arrow is normalized against. -/
  normalization : GeometricNormalization p P π F
  unitIso : DerivedCategory.Q.obj (torsionComplex p P π M U.val.unit) ≅
    unitObject (TorsionRing p P π)
  analytic_unit : IsIso (M.analytic.unit.app (unitObject (TorsionRing p P π)))
  arrow : DGHom (TorsionRing p P π) 0
    (F.compactFunctor.obj (op U.val.unit)).unop U.val.unit
  closed : dgDifferential (TorsionRing p P π) 0 arrow = 0
  cocycle : Cocycle
    (torsionComplex p P π M (F.compactFunctor.obj (op U.val.unit)).unop)
    (torsionComplex p P π M U.val.unit) 0
  realization : (cocycle : Cochain _ _ 0) = M.compact.realization.dgMap 0 arrow
  normalized : (normalization.comparison U.val.unit).hom ≫
      DerivedCategory.Q.map cocycle.homOf ≫ unitIso.hom =
    (normalization.extension.functor _ _ ⋙ M.analytic.functor).map unitIso.hom ≫
      M.analytic.functor.map (geometricUnitMap p P π h normalization.extension) ≫
        inv (M.analytic.unit.app (unitObject (TorsionRing p P π)))

/-- The model of a compact unit is geometrically normalized. -/
theorem CompactUnit.source_normalization {U : UnitInductionModel p P π M}
    (A : CompactUnit p P π h M F U) : IsGeometricallyNormalized p P π F :=
  ⟨A.normalization⟩

/-- The cofibrant source of a compact unit is exactly the coefficient representable. -/
abbrev unitSource (U : UnitInductionModel p P π M) :
    DGDerivedModules (TorsionRing p P π) M.compact.objects :=
  ⟨unitRepresentable p P π M U, unitRepresentable_cofibrant p P π M U⟩

/-- The Yoneda/adjunction-forced linearization of the coefficient representable. -/
def CompactUnit.linearization {U : UnitInductionModel p P π M}
    (A : CompactUnit p P π h M F U) :
    DGHom (TorsionRing p P π) 0
      (F.extension.functor.obj (unitSource p P π M U)).obj (unitRepresentable p P π M U) :=
  let b := ((F.restriction.value (unitRepresentable p P π M U) (op U.val.unit)).inv.f 0)
    A.arrow
  let c := ((dgRepresentableHomIso (TorsionRing p P π) U.val.unit
    (F.restriction.functor.obj (unitRepresentable p P π M U)).toEnrichedFunctor).inv.f 0) b
  ((F.extension.homIso (unitSource p P π M U) (unitRepresentable p P π M U)).inv.f 0) c

set_option maxHeartbeats 1200000 in
/-- The almost-local coefficient phi unit and the normalized localization square. The square is
stated before almost localization: the linearized structure map of the φ-object is precomposed with
the unit of the almost localization at the raw extension, the same unit that defines the enhanced
Frobenius. -/
structure AlmostUnit (U : UnitInductionModel p P π M)
    (A : CompactUnit p P π h M F U) where
  object : PhiObject p P π h M F
  localization : unitRepresentable p P π M U ⟶ object.module.obj
  almost_equivalence : IsAlmostEquivalence p P π M localization
  linearization_square :
    dgComp (C := RightModule (TorsionRing p P π) M.compact.objects)
      (X := (F.extension.functor.obj (unitSource p P π M U)).obj)
      (Y := (F.extension.functor.obj ⟨object.module.obj, object.module.property.1⟩).obj)
      (Z := object.module.obj) (TorsionRing p P π)
      (((F.extension.functor.map (unitSource p P π M U)
        ⟨object.module.obj, object.module.property.1⟩).f 0) (closedModuleHom localization))
      (closedModuleHom (C := M.compact.objects)
        (M.localization.unit (F.extension.functor.obj
          ⟨object.module.obj, object.module.property.1⟩) ≫ object.linearized)) (by omega) -
    dgComp (C := RightModule (TorsionRing p P π) M.compact.objects)
      (TorsionRing p P π) (A.linearization p P π h M F)
      (closedModuleHom localization) (by omega) ∈
        dgBoundaries (TorsionRing p P π)
          (F.extension.functor.obj (unitSource p P π M U)).obj object.module.obj

end MathlibExt.Condensed.FrobeniusCoefficientUnit

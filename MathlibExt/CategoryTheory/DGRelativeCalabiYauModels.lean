/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGBimodulePushforwardModels
public import MathlibExt.Algebra.Homology.RelativeCyclicGluing

/-!
# Actual relative left Calabi-Yau class and counit-cone diagrams

The relative class lies in the actual completed negative-cyclic cone.
Its boundary and null-homotopy are extracted from the native cone blocks
and the unit-normalized trace/duality comparison. The middle map is the
actual induced Hom map of induction and left-duality base change.

The left and right vertical maps of diagram4.10 are fixed on every
module point by the counit/dual-counit cone matrices. A candidate stores
these construction outputs, with no nondegeneracy field. Relative CY is
the separate smoothness and quasi-isomorphism predicate on all three maps.

Reference: Brav--Dyckerhoff, arXiv:1606.00619v1, equations4.9--4.10
and Definition4.11. The source base is a field, with no characteristic-zero
restriction in these relative-CY composition statements.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.DGRelativeCalabiYauModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.DGBarDiagonalModels
open MathlibExt.CategoryTheory.DGCalabiYauMapModels
open MathlibExt.CategoryTheory.DGModuleConeShiftModels
open MathlibExt.CategoryTheory.DGBimodulePushforwardModels
open MathlibExt.Algebra.Homology.DGCategoryTraceModels
open MathlibExt.Algebra.Homology.DGCyclicMixedModels
open CochainComplex.HomComplex

universe u
variable {k : Type u} [Field k]

/-- The common actual category-level bar/dual data contain no CY structure. -/
structure CYCategoryData (S : NegativeTraceSystem k) (C : DGCat k) where
  diagonal : EnvelopingModuleModel (MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels.diagonal C)
  free : FreeDiagonalSystem C
  bar : BarDiagonalModel diagonal free
  inverse : InverseDualModel bar
  evaluation : TraceEvaluationModel bar inverse (S.mixed C)
  projection : NegativeProjectionModel (S.negative C)

/-- The relative comparison is the actual bar counit and left-duality mate of the DG functor,
together with a chosen naturality homotopy for the trace square. Only the boundary of
`naturality` is constrained: different choices with the same boundary differ by a closed degree
`-1` map, and they can change the class-induced maps of `RelativeCYMapModel` even in cohomology.
Brav--Dyckerhoff (4.9) fix this square from the trace construction; here it is part of the
context, and every relative Calabi--Yau statement below is relative to this choice. -/
structure RelativeCYContext {A B : DGCat k} (S : NegativeTraceSystem k) (f : A ⟶ B)
    (DA : CYCategoryData S A) (DB : CYCategoryData S B) where
  enveloping : EnvelopingMap f
  restriction : RestrictionModel enveloping.functor
  induction : ExtensionModel enveloping.functor restriction
  barMap : BarRestrictionMapModel f enveloping restriction DA.bar DB.bar
  counit : BarCounitModel induction barMap
  dualPush : ModuleLeftDualModel B (pushedDiagonal induction DA.bar)
  dualBaseChange : DualBaseChangeModel induction DA.bar DA.inverse dualPush
  dualCounit : DualCounitModel induction counit DB.inverse dualPush
  projection_comm : (S.map f).map ≫ DB.projection.map = DA.projection.map ≫ (S.traceMap f).map
  naturality : Cochain (S.mixed A).total.complex
    (dgHomComplex k DB.inverse.replacement.module DB.bar.module) (-1)
  naturality_boundary : δ (-1) 0 naturality =
    Cochain.ofHom ((S.traceMap f).map ≫ DB.evaluation.comparison) -
      Cochain.ofHom (DA.evaluation.comparison ≫
        phiTransfer induction counit dualBaseChange dualCounit)

/-- Relative negative cyclic is the literal cofiber of the actual completed coefficient map. -/
def relativeNegativeComplex {A B : DGCat k} (S : NegativeTraceSystem k) (f : A ⟶ B) : Cochains k :=
  CochainComplex.mappingCone (S.map f).map

/-- The source relative class is k[n]→CC(B,A)[[u]], with all compatibility cochains retained. -/
abbrev RelativeNegativeClass {A B : DGCat k} (S : NegativeTraceSystem k) (f : A ⟶ B) (n : ℤ) :=
  (𝟙_ (Cochains k))⟦n⟧ ⟶ relativeNegativeComplex S f

/-- The actual boundary coefficient in the relative negative-cyclic cone. -/
def relativeBoundaryValue {A B : DGCat k} {S : NegativeTraceSystem k} {f : A ⟶ B}
    {n : ℤ} (a : RelativeNegativeClass S f n) (u : ((𝟙_ (Cochains k))⟦n⟧).X (-n)) :
    (S.negative A).complex.X (1 - n) :=
  degreeCast (S.negative A).complex (by omega)
    ((CochainComplex.mappingCone.fst (S.map f).map).val.v (-n) (-n + 1) rfl ((a.f (-n)) u))

/-- The actual null-homotopy coefficient, including the full relative class. -/
def relativeInteriorValue {A B : DGCat k} {S : NegativeTraceSystem k} {f : A ⟶ B}
    {n : ℤ} (a : RelativeNegativeClass S f n) (u : ((𝟙_ (Cochains k))⟦n⟧).X (-n)) :
    (S.negative B).complex.X (-n) :=
  (CochainComplex.mappingCone.snd (S.map f).map).v (-n) (-n) (by omega) ((a.f (-n)) u)

/-- The actual two counit cones and target shifts form the source diagram4.10. -/
structure RelativeConeContext {A B : DGCat k} {S : NegativeTraceSystem k} {f : A ⟶ B}
    {DA : CYCategoryData S A} {DB : CYCategoryData S B} (F : RelativeCYContext S f DA DB) (n : ℤ) where
  coneCounit : CofibrantConeModel (pushedDiagonal F.induction DA.bar)
    (⟨DB.bar.module, DB.bar.cofibrant⟩ : DGDerivedModules k (enveloping B B)) F.counit.map
  coneDual : CofibrantConeModel
    (⟨DB.inverse.replacement.module, DB.inverse.replacement.cofibrant⟩ : DGDerivedModules k (enveloping B B))
    (⟨F.dualPush.replacement.module, F.dualPush.replacement.cofibrant⟩ : DGDerivedModules k (enveloping B B))
    F.dualCounit.map
  leftShift : CofibrantShiftModel
    (⟨coneCounit.module, coneCounit.cofibrant⟩ : DGDerivedModules k (enveloping B B)) (-n)
  middleShift : CofibrantShiftModel (pushedDiagonal F.induction DA.bar) (1 - n)
  rightShift : CofibrantShiftModel
    (⟨DB.bar.module, DB.bar.cofibrant⟩ : DGDerivedModules k (enveloping B B)) (1 - n)

/-- A relative candidate has the source class's actual boundary, null-homotopy and cone maps.
It contains no quasi-isomorphism or nondegeneracy conclusion. -/
structure RelativeCYMapModel {A B : DGCat k} {S : NegativeTraceSystem k} {f : A ⟶ B}
    {DA : CYCategoryData S A} {DB : CYCategoryData S B} (F : RelativeCYContext S f DA DB)
    (n : ℤ) (a : RelativeNegativeClass S f n) (C : RelativeConeContext F n) where
  boundary : DGHom k (1 - n) DA.inverse.replacement.module DA.bar.module
  boundary_closed : dgDifferential k (1 - n) boundary = 0
  boundary_eq : ∀ u : ((𝟙_ (Cochains k))⟦n⟧).X (-n),
    ((DA.evaluation.comparison.f (1 - n))
      ((DA.projection.map.f (1 - n)) (relativeBoundaryValue a u))) =
      shiftedUnitScalar k n u • boundary
  nullhomotopy : DGHom k (-n) DB.inverse.replacement.module DB.bar.module
  nullhomotopy_eq : ∀ u : ((𝟙_ (Cochains k))⟦n⟧).X (-n),
    ((DB.evaluation.comparison.f (-n))
      ((DB.projection.map.f (-n)) (relativeInteriorValue a u))) +
      F.naturality.v (1 - n) (-n) (by omega)
        ((DA.projection.map.f (1 - n)) (relativeBoundaryValue a u)) =
      shiftedUnitScalar k n u • nullhomotopy
  nullhomotopy_boundary : dgDifferential k (-n) nullhomotopy =
    -degreeCast (dgHomComplex k DB.inverse.replacement.module DB.bar.module) (by omega)
      ((phiTransfer F.induction F.counit F.dualBaseChange F.dualCounit).f (1 - n) boundary)
  middle : F.dualPush.replacement.module ⟶ C.middleShift.module
  middle_eq : ∀ (x : B) (y : Bᵒᵖ) (r : ℤ),
    (moduleComponent middle (moduleIndex B B x y)).f r ≫
      (C.middleShift.valueIso (moduleIndex B B x y)).hom.f r ≫
      (((pushedDiagonal F.induction DA.bar).obj.toEnrichedFunctor.obj (moduleIndex B B x y)).shiftFunctorObjXIso
        (1 - n) r (r + 1 - n) (by omega)).hom =
      (DGFunctor.dgApp k (1 - n) (moduleIndex B B x y)
        ((phiMiddle F.induction F.dualBaseChange).f (1 - n) boundary) : Cochain _ _ (1 - n)).v
          r (r + 1 - n) (by omega)
  left : DB.inverse.replacement.module ⟶ C.leftShift.module
  left_eq : ∀ (x : B) (y : Bᵒᵖ) (r : ℤ),
    (moduleComponent left (moduleIndex B B x y)).f r ≫
      (C.leftShift.valueIso (moduleIndex B B x y)).hom.f r ≫
      ((C.coneCounit.valueIso (moduleIndex B B x y)).hom⟦-n⟧').f r ≫
      ((CochainComplex.mappingCone (moduleComponent F.counit.map (moduleIndex B B x y))).shiftFunctorObjXIso
        (-n) r (r - n) (by omega)).hom =
      (DGFunctor.dgApp k (1 - n) (moduleIndex B B x y)
        (dgComp k (moduleCycle F.dualCounit.map)
          ((phiMiddle F.induction F.dualBaseChange).f (1 - n) boundary) (by omega)) : Cochain _ _ (1 - n)).v
          r (r - n + 1) (by omega) ≫
        (CochainComplex.mappingCone.inl (moduleComponent F.counit.map (moduleIndex B B x y))).v
          (r - n + 1) (r - n) (by omega) +
      (DGFunctor.dgApp k (-n) (moduleIndex B B x y) nullhomotopy : Cochain _ _ (-n)).v
        r (r - n) (by omega) ≫
        (CochainComplex.mappingCone.inr (moduleComponent F.counit.map (moduleIndex B B x y))).f (r - n)
  right : C.coneDual.module ⟶ C.rightShift.module
  right_eq : ∀ (x : B) (y : Bᵒᵖ) (r : ℤ),
    (moduleComponent right (moduleIndex B B x y)).f r ≫
      (C.rightShift.valueIso (moduleIndex B B x y)).hom.f r ≫
      ((DB.bar.module.toEnrichedFunctor.obj (moduleIndex B B x y)).shiftFunctorObjXIso
        (1 - n) r (r + 1 - n) (by omega)).hom =
      (C.coneDual.valueIso (moduleIndex B B x y)).hom.f r ≫
        ((CochainComplex.mappingCone.fst (moduleComponent F.dualCounit.map (moduleIndex B B x y))).val.v
          r (r + 1) rfl ≫
            (n.negOnePow • (DGFunctor.dgApp k (-n) (moduleIndex B B x y) nullhomotopy : Cochain _ _ (-n)).v
              (r + 1) (r + 1 - n) (by omega)) +
          (CochainComplex.mappingCone.snd (moduleComponent F.dualCounit.map (moduleIndex B B x y))).v r r (by omega) ≫
            (DGFunctor.dgApp k (1 - n) (moduleIndex B B x y)
              (dgComp k ((phiMiddle F.induction F.dualBaseChange).f (1 - n) boundary)
                (moduleCycle F.counit.map) (by omega)) : Cochain _ _ (1 - n)).v r (r + 1 - n) (by omega))

/-- The relative CY condition tests all three actual vertical module maps, over a field. The maps
are built from the naturality homotopy chosen in the context `F`, so the condition is relative to
that chosen square rather than to the class alone. -/
def IsRelativeCalabiYau {A B : DGCat k} {S : NegativeTraceSystem k} {f : A ⟶ B}
    {DA : CYCategoryData S A} {DB : CYCategoryData S B} {F : RelativeCYContext S f DA DB}
    {n : ℤ} {a : RelativeNegativeClass S f n} {C : RelativeConeContext F n}
    (M : RelativeCYMapModel F n a C) : Prop :=
  IsHomologicallySmooth A DA.diagonal ∧ IsHomologicallySmooth B DB.diagonal ∧
    ∀ i : (enveloping B B)ᵒᵖ,
      QuasiIso (moduleComponent M.left i) ∧ QuasiIso (moduleComponent M.middle i) ∧
        QuasiIso (moduleComponent M.right i)

end MathlibExt.CategoryTheory.DGRelativeCalabiYauModels

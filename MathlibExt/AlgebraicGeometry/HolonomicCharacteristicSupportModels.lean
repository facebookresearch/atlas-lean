/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticChartDifferentialOperators
public import MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModuleModels
public import MathlibExt.AlgebraicGeometry.HolomorphicCoefficientRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import MathlibExt.AlgebraicGeometry.NativeCoefficientModuleStalks
public import MathlibExt.CategoryTheory.NativeBoundedBimoduleModels
public import MathlibExt.AlgebraicGeometry.GeometricDModuleFiltrations

/-!
# Actual local good filtrations and characteristic-symbol support

Filtrations are O-subobjects of the actual native restriction N.over(U).
Goodness includes local finite free cokernel presentations, local
exhaustivity, order-compatible action and shifted finite D generators.
Graded pieces are the native consecutive cokernels. Their native germs
form the actual direct sum on which the symbol polynomial ring acts.
Constants and variables are normalized on every original filtration
section/germ, so the symbol action is not an independently chosen module.
The characteristic support and dimension use its computed annihilator,
actual PrimeSpectrum zero locus and native quotient Krull dimension.
Holonomicity requires these local conditions at every original point.

Source: DK1311.2374v2 Sections2.5,9.1,9.5 and ordinary analytic
D-module good-filtration/characteristic-symbol background. Native sheaf
modules, cokernels, germs, polynomial action, annihilator and dimension:
Mathlib56a005, Apache2.0, Andrew Yang and the Mathlib contributors.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HolonomicCharacteristicSupportModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite TopologicalSpace
open NativeIndDifferentialContexts HarmonicHolomorphicModuleModels
open AnalyticChartDifferentialOperators DifferentialOperatorSheaves DifferentialOperatorScalars
open scoped Manifold ContDiff BigOperators DirectSum

variable (n : ℕ) (M : Type) [TopologicalSpace M]
  [ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates n) M]
  [IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) ∞ M]
  [HolomorphicCoefficientSheaves.SheafCondition
    (TemperedDistributionSectionModels.ComplexCoordinates n) M]
  [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
  [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ U : Opens M, HasWeakSheafify ((Opens.grothendieckTopology M).over U) AddCommGrpCat.{0}]
  [∀ U : Opens M, ((Opens.grothendieckTopology M).over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ (U : Opens M) (V : Over U), HasWeakSheafify
    (((Opens.grothendieckTopology M).over U).over V) AddCommGrpCat.{0}]
  [∀ (U : Opens M) (V : Over U),
    (((Opens.grothendieckTopology M).over U).over V).WEqualsLocallyBijective AddCommGrpCat.{0}]

abbrev RawO := holomorphicStructureRing (n := n) (M := M)
abbrev NativeDModule := DModule ℂ M (analyticCoefficients n M)

/-- The shared holomorphic coefficient map (`HolomorphicCoefficientRestriction`). -/
abbrev rawCoefficientMap : RawO n M ⟶ coefficientSheaf ℂ M (analyticCoefficients n M) :=
  HolomorphicCoefficientRestriction.holomorphicCoefficientMap n M

/-- The shared restriction of a D-module to the holomorphic functions. -/
abbrev underlyingRawO (N : NativeDModule n M) : SheafOfModules.{0} (RawO n M) :=
  HolomorphicCoefficientRestriction.holomorphicRestriction n M N

variable (N : NativeDModule n M) (U : Opens M)

def InLocalFiltration (F : ℤ → Subobject ((underlyingRawO n M N).over U))
    (p : ℤ) (V : Opens M) (hV : V ≤ U) (s : N.val.obj (op V)) : Prop :=
  ∃ t : (Subobject.underlying.obj (F p)).val.obj (op (Over.mk (homOfLE hV))),
    ((F p).arrow.val.app (op (Over.mk (homOfLE hV)))).hom t = s

/-- A genuinely local good filtration on the actual native restricted module. The generators
generate each filtration piece as a sheaf: every section is, near each point, a combination of the
restricted generators with operators of the allowed orders. -/
structure LocalGoodFiltration where
  term : ℤ → Subobject ((underlyingRawO n M N).over U)
  monotone : Monotone term
  boundedBelow : ∃ p : ℤ, ∀ q < p, term q = ⊥
  locallyPresented : ∀ (p : ℤ) (x : M), x ∈ U →
    ∃ (V : Opens M) (hV : V ≤ U), x ∈ V ∧
      ∃ (a b : ℕ)
        (f : SheafOfModules.free (R := ((RawO n M).over U).over (Over.mk (homOfLE hV)))
            (Fin a) ⟶
          SheafOfModules.free (R := ((RawO n M).over U).over (Over.mk (homOfLE hV))) (Fin b))
        (pi : SheafOfModules.free (R := ((RawO n M).over U).over (Over.mk (homOfLE hV)))
            (Fin b) ⟶ (Subobject.underlying.obj (term p)).over (Over.mk (homOfLE hV)))
        (h : f ≫ pi = 0), Nonempty (IsColimit (CokernelCofork.ofπ pi h))
  exhaustive : ∀ (V : Opens M) (hV : V ≤ U) (s : N.val.obj (op V)) (x : V),
    ∃ (W : Opens M) (hW : W ≤ V), x.val ∈ W ∧ ∃ p : ℤ,
      InLocalFiltration n M N U term p W (hW.trans hV)
        ((N.val.map (homOfLE hW).op).hom s)
  orderAction : ∀ (V : Opens M) (hV : V ≤ U) (p : ℤ) (d : ℕ)
      (P : finiteOperatorRing ℂ M (analyticCoefficients n M) V),
      GeometricDModuleFiltrations.OrderOn
        (TemperedDistributionSectionModels.ComplexCoordinates n) M P d →
      ∀ s : N.val.obj (op V), InLocalFiltration n M N U term p V hV s →
        InLocalFiltration n M N U term (p + d) V hV
          (GeometricDModuleFiltrations.act
            (TemperedDistributionSectionModels.ComplexCoordinates n) M N P s)
  localGenerators : ∀ x : M, x ∈ U → ∃ (V : Opens M) (hV : V ≤ U), x ∈ V ∧
    ∃ (r : ℕ) (degree : Fin r → ℤ) (g : Fin r → N.val.obj (op V)),
      (∀ j, InLocalFiltration n M N U term (degree j) V hV (g j)) ∧
      ∀ (W : Opens M) (hW : W ≤ V) (p : ℤ) (s : N.val.obj (op W)),
        InLocalFiltration n M N U term p W (hW.trans hV) s →
        ∀ y : W, ∃ (W' : Opens M) (hW' : W' ≤ W), y.val ∈ W' ∧
          ∃ (d : Fin r → ℕ) (P : Fin r → finiteOperatorRing ℂ M (analyticCoefficients n M) W'),
            (∀ j, P j = 0 ∨
              (GeometricDModuleFiltrations.OrderOn
                (TemperedDistributionSectionModels.ComplexCoordinates n) M (P j) (d j) ∧
                  (d j : ℤ) + degree j ≤ p)) ∧
            (N.val.map (homOfLE hW').op).hom s = ∑ j, GeometricDModuleFiltrations.act
              (TemperedDistributionSectionModels.ComplexCoordinates n) M N (P j)
                ((N.val.map (homOfLE (hW'.trans hW)).op).hom (g j))

variable (G : LocalGoodFiltration n M N U)

def localStep (p : ℤ) : Subobject.underlying.obj (G.term (p - 1)) ⟶
    Subobject.underlying.obj (G.term p) :=
  Subobject.underlying.map (homOfLE (G.monotone (by omega)))

def localGraded (p : ℤ) : SheafOfModules.{0} ((RawO n M).over U) :=
  cokernel (localStep n M N U G p)

def extendLocalO : SheafOfModules.{0} ((RawO n M).over U) ⥤ SheafOfModules.{0} (RawO n M) :=
  SheafOfModules.pushforward (SheafOfModules.pushforwardOver (R := RawO n M) U)

def gradedAmbient (p : ℤ) : SheafOfModules.{0} (RawO n M) :=
  (extendLocalO n M U).obj (localGraded n M N U G p)

def overProjection (V : Opens M) (hV : V ≤ U) :
    (Over.star U).obj V ⟶ Over.mk (homOfLE hV) :=
  Over.homMk (Limits.prod.snd (X := U) (Y := V)) (Subsingleton.elim _ _)

def ambientLocalSection (F : SheafOfModules.{0} ((RawO n M).over U))
    (V : Opens M) (hV : V ≤ U) (s : F.val.obj (op (Over.mk (homOfLE hV)))) :
    ((extendLocalO n M U).obj F).val.obj (op V) :=
  (F.val.map (overProjection M U V hV).op).hom s

def gradedSection (p : ℤ) (V : Opens M) (hV : V ≤ U)
    (s : (Subobject.underlying.obj (G.term p)).val.obj (op (Over.mk (homOfLE hV)))) :
    (gradedAmbient n M N U G p).val.obj (op V) :=
  ambientLocalSection n M U (localGraded n M N U G p) V hV
    (((cokernel.π (localStep n M N U G p)).val.app (op (Over.mk (homOfLE hV)))).hom s)

abbrev commutativeCoefficients : (Opens M)ᵒᵖ ⥤ CommRingCat.{0} :=
  analyticCoefficients n M ⋙ forget₂ (CommAlgCat.{0} ℂ) CommRingCat.{0}

abbrev ScalarStalk (x : M) : Type :=
  ↑(TopCat.Presheaf.stalk (C := CommRingCat.{0}) (X := TopCat.of M) (commutativeCoefficients n M) x)
abbrev GradedStalk (x : M) (p : ℤ) : Type :=
  ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := TopCat.of M)
    (gradedAmbient n M N U G p).val.presheaf x)

local instance gradedStalkModule (x : M) (p : ℤ) :
    Module (ScalarStalk n M x) (GradedStalk n M N U G x p) := by
  let F : PresheafOfModules.{0}
      (commutativeCoefficients n M ⋙ forget₂ CommRingCat.{0} RingCat.{0}) :=
    (gradedAmbient n M N U G p).val
  exact NativeCoefficientModuleStalks.actualStalkModule (TopCat.of M) (commutativeCoefficients n M) F x

abbrev SymbolRing (x : M) := MvPolynomial (Fin n) (ScalarStalk n M x)
abbrev SymbolModule (x : M) := ⨁ p : ℤ, GradedStalk n M N U G x p

def gradedGerm (x : M) (p : ℤ) (V : Opens M) (hV : V ≤ U) (hx : x ∈ V)
    (s : (Subobject.underlying.obj (G.term p)).val.obj (op (Over.mk (homOfLE hV)))) :
    GradedStalk n M N U G x p :=
  TopCat.Presheaf.germ (X := TopCat.of M) (gradedAmbient n M N U G p).val.presheaf V x hx
    (gradedSection n M N U G p V hV s)

variable (x : M) (hx : x ∈ U)

/-- The polynomial symbol action is fixed on the original quotient/germ generators. -/
structure SymbolAtPointSource (_hx : x ∈ U) where
  neighborhood : Opens M
  inside : neighborhood ≤ U
  contains : x ∈ neighborhood
  chart : (neighborhood : Set M) ⊆
    (chartAt (TemperedDistributionSectionModels.ComplexCoordinates n) x).source
  operators : ChartOperatorSource n M (analyticCoefficients n M)
    (holomorphicChartValue n M) false x neighborhood chart
  [symbolAction : Module (SymbolRing n M x) (SymbolModule n M N U G x)]
  constants : ∀ (a : ScalarStalk n M x) (p : ℤ) (s : GradedStalk n M N U G x p),
    (MvPolynomial.C a : SymbolRing n M x) •
      DirectSum.lof (ScalarStalk n M x) ℤ (GradedStalk n M N U G x) p s =
      DirectSum.lof (ScalarStalk n M x) ℤ (GradedStalk n M N U G x) p (a • s)
  coordinateValues : ∀ (i : Fin n) (p : ℤ) (V : Opens M) (hV : V ≤ neighborhood) (hX : x ∈ V)
      (s : (Subobject.underlying.obj (G.term p)).val.obj (op (Over.mk (homOfLE (hV.trans inside)))))
      (t : (Subobject.underlying.obj (G.term (p + 1))).val.obj
        (op (Over.mk (homOfLE (hV.trans inside))))),
    ((G.term (p + 1)).arrow.val.app (op (Over.mk (homOfLE (hV.trans inside))))).hom t =
      GeometricDModuleFiltrations.act (TemperedDistributionSectionModels.ComplexCoordinates n) M N
        (restrictFinite ℂ M (analyticCoefficients n M) hV (operators.coordinateOperator i))
        (((G.term p).arrow.val.app (op (Over.mk (homOfLE (hV.trans inside))))).hom s) →
      (MvPolynomial.X i : SymbolRing n M x) •
        DirectSum.lof (ScalarStalk n M x) ℤ (GradedStalk n M N U G x) p
        (gradedGerm n M N U G x p V (hV.trans inside) hX s) =
          DirectSum.lof (ScalarStalk n M x) ℤ (GradedStalk n M N U G x) (p + 1)
            (gradedGerm n M N U G x (p + 1) V (hV.trans inside) hX t)

variable (S : SymbolAtPointSource n M N U G x hx)

def characteristicIdeal : Ideal (SymbolRing n M x) :=
  letI := S.symbolAction
  Module.annihilator (SymbolRing n M x) (SymbolModule n M N U G x)

def characteristicSupport : Set (PrimeSpectrum (SymbolRing n M x)) :=
  PrimeSpectrum.zeroLocus (characteristicIdeal n M N U G x hx S : Set (SymbolRing n M x))

def HasHolonomicSymbolDimension : Prop :=
  ringKrullDim ((SymbolRing n M x) ⧸ characteristicIdeal n M N U G x hx S) ≤ (n : WithBot ℕ∞)

/-- Holonomicity uses actual local good filtrations and computed characteristic support at every point. -/
def IsHolonomic : Prop :=
  ∀ x : M, ∃ U : Opens M, ∃ hx : x ∈ U, ∃ G : LocalGoodFiltration n M N U,
    ∃ S : SymbolAtPointSource n M N U G x hx, HasHolonomicSymbolDimension n M N U G x hx S

attribute [local instance] HasDerivedCategory.standard

/-- Bounded holonomic complexes are defined through their original native D-module cohomology. -/
def IsBoundedHolonomic : ObjectProperty (DerivedCategory (NativeDModule n M)) := fun K =>
  MathlibExt.CategoryTheory.NativeBoundedBimoduleModels.IsBoundedDerived (NativeDModule n M) K ∧
    ∀ i : ℤ, IsHolonomic n M ((DerivedCategory.homologyFunctor (NativeDModule n M) i).obj K)

abbrev HolonomicDerived := (IsBoundedHolonomic n M).FullSubcategory

end MathlibExt.AlgebraicGeometry.HolonomicCharacteristicSupportModels

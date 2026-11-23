/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiSourceDGNormalizationModels
public import MathlibExt.AlgebraicGeometry.LiCentralSourceModels
public import MathlibExt.AlgebraicGeometry.LiSourceQualifiedVirtualModels
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-!
# Source-qualified relative and central DG virtual interfaces

Both outputs use the full native coefficient Context and the SAME
global injectiveMap P to canonical cotangent. The comparison is an
equality of whole DG natural transformations. The source tensor is
normalized over every coefficient degree, native family/refinement,
universal/trivial curve lift and actual nonsplit polynomial class.

The central source is literally cone(original derivative)[-1]. Its
obstruction point has BOTH its actual lifted-map Cech coordinate and
the kernel class of the original product of expanded parameters. The
latter rules out a free modification of the central base component.

All data are construction outputs of the final Wanted virtual catalogue.
Source: Jun Li math/0110113v1, (1.15)--(1.25), Proposition2.4,
Theorems2.3/2.5 and Theorem3.15; native PR4048
e6e3c8d7c02b1baedace4e3044e622070b5217d0.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiQualifiedDGVirtualModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry
open GeneralStackGeometry StackCycleGeometry StackAffineModules StackCycleRelations StackChowGroups
open ExpandedTargetChainGeometry ExpandedTargetGluingModels RelativeProjectiveLineModels
open StandardRelativeExpansionModels LiGluingRelativeTypes LiExpandedDegenerationModels
open LiGenericSourceIndex LiGenericSourceAssemblyModels LiSourceDGNormalizationModels
open LiDGAssignmentModels CochainComplex.HomComplex
open scoped Simplicial TensorProduct BigOperators

variable {k : Type} [Field k]

section Relative

variable {P : RelativePair (k := k)} {R : ProjectiveLine P.divisor.left (normalLineModule P)}
  {S : StandardRelativeExpansionModels.StandardSystem P R} {n r : ℕ} {G : FullType n r}
  [LocallyOfFiniteType P.target.hom] [IsNoetherian P.target.left]
  {beta : Fin G.vertices → StableMapNumericalClasses.NumericalClass P.target.left}
  {M : ModuliModel P R S G beta}
  (N : LiRelativeSourceModels.Source P R S G beta M)
  {D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)} {K : KreschPresentation D}
  {Z : RubberVirtualClassModels.Point D K}
  (V : LiSourceQualifiedVirtualModels.VirtualData N.assembly.parentModel D K M.finiteType Z)

/-- The full relative port is constructed from that SAME interpreted relative source. -/
structure Relative where
  assignment : Assignment V.dual
  port : SourcePort (A := assignment)
    (LiRelativeSourceModels.QualifiedFrame P R S G beta M)
    (LiRelativeSourceModels.gauge P R S G beta M) N.assembly.native.global
    (nativeChartMap N.assembly.native)
  moduleQuasi : ∀ (C : SourceChart M.stack) (h : LiRelativeSourceModels.QualifiedFrame P R S G beta M C)
    (I : ModuleCat.{0} C.ring) (m : ℤ),
    QuasiIso ((port.chart C h).localSource.read (nativeChartMap N.assembly.native C h)
      (unitCoefficient C I m))

end Relative

section Central

variable {P Q : RelativePair (k := k)} {W0 : SingularTarget P Q}
  {W : OneParameter P Q W0} {S : LiExpandedDegenerationModels.StandardSystem W} {n g : ℕ}
  [LocallyOfFiniteType W0.scheme.hom] [IsNoetherian W0.scheme.left]
  {beta : StableMapNumericalClasses.NumericalClass W0.scheme.left}
  {M : LiExpandedCentralModels.ModuliModel W S n g beta}
  (N : LiCentralSourceModels.Source W S beta M)
  {D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)} {K : KreschPresentation D}
  {Z : RubberVirtualClassModels.Point D K}
  (V : LiSourceQualifiedVirtualModels.VirtualData N.parentModel D K M.finiteType Z)

/-- The actual cochain projection cone(derivative)[-1] to the original total source.
The minus cancels Mathlib's left-shift sign, so this is the literal cone first projection. -/
def centralProjection : LiCentralSourceModels.centralComplex W S beta M N.derivative ⟶
    N.total.native.global :=
  -Cocycle.homOf ((CochainComplex.mappingCone.fst N.derivative.map).leftShift (-1) 0 (by omega))

def centralChartMap (C : SourceChart M.stack) (h : LiCentralSourceModels.QualifiedFrame W S beta M C) :
    evaluatePoint (LiCentralSourceModels.centralComplex W S beta M N.derivative) C ⟶
      rawUnit C (LiCentralSourceModels.gauge W S beta M C h) :=
  ((pointEvaluation C).mapHomologicalComplex (ComplexShape.up ℤ)).map (centralProjection N) ≫
    nativeChartMap N.total.native C h

/-- Reading the base coordinate is the actual native cone second projection in degree one. -/
def centralBaseValue (C : SourceChart M.stack)
    (x : (pointSource (LiCentralSourceModels.centralComplex W S beta M N.derivative) C).X 1) : C.ring :=
  (Scheme.ΓSpecIso (.of C.ring)).hom.hom
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1
      (PresheafOfModules.unit (rings M.stack ⋙ forget₂ CommRingCat RingCat))).hom.app (op C.native)
      (((CochainComplex.mappingCone.snd N.derivative.map).v 1 1 (add_zero 1)).app (op C.native)
        (show ((CochainComplex.mappingCone N.derivative.map).X 1).obj (op C.native) from x)))

/-- The actual reference lift of one expanded parameter on the parent label. -/
def referenceParameter (C : SourceChart M.stack) (h : LiCentralSourceModels.QualifiedFrame W S beta M C)
    (E : AffineSquareZeroCotangentClasses.Extension k C.ring) (Q : LiNonsplitSourceModels.System C E)
    (i : Fin (h.down.gauge.gauge.rank + 1)) : E.ring :=
  (Scheme.ΓSpecIso (.of E.ring)).hom.hom
    ((Q.base.parent.inv ≫ Q.parameters none ≫ h.down.parameter.hom.left ≫
      (baseToParameters W h.down.gauge.gauge.rank).left).appTop.hom
        (parameterSection h.down.gauge.gauge.rank i))

/-- The full central port fixes the particular central map, including its nonsplit base coordinate. -/
structure Central where
  assignment : Assignment V.dual
  port : SourcePort (A := assignment)
    (LiCentralSourceModels.QualifiedFrame W S beta M)
    (LiCentralSourceModels.gauge W S beta M)
    (LiCentralSourceModels.centralComplex W S beta M N.derivative) (centralChartMap N)
  baseCoordinate : ∀ (C : SourceChart M.stack) (h : LiCentralSourceModels.QualifiedFrame W S beta M C)
    (I : ModuleCat.{0} C.ring),
    Cochain ((port.chart C h).localSource.functor.obj (unitCoefficient C I (-1)))
      (unitCoefficient C I 0) 0
  base_pure : ∀ (C : SourceChart M.stack) (h : LiCentralSourceModels.QualifiedFrame W S beta M C)
    (I : ModuleCat.{0} C.ring)
    (x : (pointSource (LiCentralSourceModels.centralComplex W S beta M N.derivative) C).X 1) (y : I),
    (baseCoordinate C h I).v 0 0 (add_zero 0)
      ((eqToHom ((port.chart C h).localSource.objects (unitCoefficient C I (-1))).symm).f 0
        (HomologicalComplex.ιTensorObj
          (pointSource (LiCentralSourceModels.centralComplex W S beta M N.derivative) C)
          (unitCoefficient C I (-1)) 1 (-1) 0 (by omega)
            (x ⊗ₜ[C.ring] (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1) I).inv y))) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 I).inv (centralBaseValue N C x • y)
  originalKernel : ∀ (C : SourceChart M.stack) (h : LiCentralSourceModels.QualifiedFrame W S beta M C)
    (T : PolynomialTest V.coefficients V.cotangent C)
    (E : AffineSquareZeroCotangentClasses.Extension (GlobalStackCotangentModels.baseRing T.chart) C.ring)
    (Q : LiNonsplitSourceModels.System C (T.extension E)), RingHom.ker E.projection.toRingHom
  original_value : ∀ C h T E Q,
    (originalKernel C h T E Q).val =
      ∏ i : Fin (h.down.gauge.gauge.rank + 1), referenceParameter C h (T.extension E) Q i
  nonsplit_base : ∀ C h T E Q,
    (baseCoordinate C h E.coefficient).v 0 0 (add_zero 0)
      (((port.chart C h).nonsplitPoint T E Q).f 0 (unitGenerator C)) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 E.coefficient).inv
        (E.kernel (originalKernel C h T E Q))

end Central

end MathlibExt.AlgebraicGeometry.LiQualifiedDGVirtualModels

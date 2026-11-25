/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SchemeFirstOrderDifferentials
public import MathlibExt.AlgebraicGeometry.QuasicoherentDualityReferences
public import MathlibExt.Algebra.Homology.PerfectTorsionDeterminants
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Actual nodal-map branch complexes

Relative differentials are the native cokernel of the base differential.
Their map is fixed by the actual Kähler derivative and quotient maps.
The nodal fundamental class is tested on a covering collection of actual
étale xy=a charts: dx maps to xω and dy to -yω. Its target is the actual
H^-1 of the proper relative duality object. Local generator changes are
units and preserve the resulting perfect-complex divisor.

The branch object is the actual Rf_* of the cone of
f*Ω_(D×T)/T → ω_C/T in degrees [-1,0]. This keeps contracted components,
nodes, and nonreduced bases in the source construction.
Reference: Fantechi–Pandharipande math/9905104v1, §§2.3–3.2.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HurwitzBranchComplexes

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.AlgebraicDifferentialSheaves
open MathlibExt.AlgebraicGeometry.LocalDifferentialPullbacks
open MathlibExt.AlgebraicGeometry.GenericSectionMaps
open MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies
open MathlibExt.AlgebraicGeometry.QuasicoherentDualityReferences
open MathlibExt.AlgebraicGeometry.BirationalDualityReferences
attribute [local instance] HasDerivedCategory.standard

variable {k : Type} [CommRing k]

/-- Actual relative one-forms, retaining the literal base differential. -/
structure RelativeFormsData (C T : Over (Spec (.of k))) (p : C ⟶ T) where
  differential : PullbackDifferential T p

def relativeForms {C T : Over (Spec (.of k))} {p : C ⟶ T} (D : RelativeFormsData C T p) :
    C.left.Modules := cokernel D.differential.map

def relativeDifferential {C T : Over (Spec (.of k))} {p : C ⟶ T}
    (D : RelativeFormsData C T p) (U : C.left.Opens) (a : Γ(C.left,U)) :
    Γ(relativeForms D,U) := (cokernel.π D.differential.map).app U (differential C U a)

/-- The relative derivative is fixed by the actual absolute Kähler map and both cokernels. -/
structure RelativeFormsMap {C Y T : Over (Spec (.of k))} {p : C ⟶ T} {q : Y ⟶ T}
    (f : C ⟶ Y) (over : f ≫ q = p) (D : RelativeFormsData C T p) (E : RelativeFormsData Y T q) where
  differential : PullbackDifferential Y f
  map : (Scheme.Modules.pullback f.left).obj (relativeForms E) ⟶ relativeForms D
  normalized : (Scheme.Modules.pullback f.left).map (cokernel.π E.differential.map) ≫ map =
    differential.map ≫ cokernel.π D.differential.map

/-- The actual relative node ring, including a nonreduced base or smoothing parameter. -/
abbrev RelativeNodeRing (R : Type) [CommRing R] (a : R) :=
  MvPolynomial (Fin 2) R ⧸ Ideal.span
    {MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) - MvPolynomial.C a}

def relativeNode (R : Type) [CommRing R] (a : R) : Scheme.{0} := Spec (.of (RelativeNodeRing R a))

def nodeProjection (R : Type) [CommRing R] (a : R) : relativeNode R a ⟶ Spec (.of R) :=
  Spec.algebraMap R (RelativeNodeRing R a)

def nodeCoordinate (R : Type) [CommRing R] (a : R) (i : Fin 2) : RelativeNodeRing R a :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

/-- An actual étale relative-node chart at an actual source point. -/
structure NodeChart {C T : Over (Spec (.of k))} {p : C ⟶ T}
    (D : RelativeFormsData C T p) (ω : C.left.Modules) (x : C.left) where
  ring : Type
  [commRing : CommRing ring]
  parameter : ring
  Y : Scheme.{0}
  node : Y ⟶ relativeNode ring parameter
  [nodeEtale : Etale node]
  source : Y ⟶ C.left
  [sourceEtale : Etale source]
  base : Spec (.of ring) ⟶ T.left
  [baseEtale : Etale base]
  over : source ≫ p.left = node ≫ nodeProjection ring parameter ≫ base
  point : Y
  contains : source point = x
  forms : (Scheme.Modules.pullback source).obj (relativeForms D) ≅
    AlgebraicDifferentialSheaves.forms ring (Over.mk (node ≫ nodeProjection ring parameter)) 1
  forms_normalized : ∀ (U : C.left.Opens) (W : Y.Opens) (h : W ≤ source ⁻¹ᵁ U)
    (a : Γ(C.left,U)),
    (forms.hom.app W) (localPullbackSection source (relativeForms D) U W h
      (relativeDifferential D U a)) =
    differential (Over.mk (node ≫ nodeProjection ring parameter)) W ((source.appLE U W h).hom a)
  canonical : (Scheme.Modules.pullback source).obj ω ≅ structureModule Y

attribute [instance] NodeChart.commRing NodeChart.nodeEtale NodeChart.sourceEtale
  NodeChart.baseEtale

def NodeChart.coordinate {C T : Over (Spec (.of k))} {p : C ⟶ T}
    {D : RelativeFormsData C T p} {ω : C.left.Modules} {x : C.left}
    (a : NodeChart D ω x) (i : Fin 2) : Γ(a.Y, ⊤) :=
  a.node.appTop.hom ((Scheme.ΓSpecIso (.of (RelativeNodeRing a.ring a.parameter))).inv.hom
    (nodeCoordinate a.ring a.parameter i))

/-- The fundamental class has the actual node Jacobian on a covering étale atlas. -/
structure NodalFundamentalClass {C T : Over (Spec (.of k))} {p : C ⟶ T}
    (D : RelativeFormsData C T p) (ω : C.left.Modules) where
  map : relativeForms D ⟶ ω
  chart : ∀ x : C.left, NodeChart D ω x
  x_normalized : ∀ x : C.left,
    ((((Scheme.Modules.pullback (chart x).source).map map) ≫ (chart x).canonical.hom).app ⊤)
      (((chart x).forms.inv.app ⊤)
        (differential (Over.mk ((chart x).node ≫ nodeProjection (chart x).ring (chart x).parameter))
          ⊤ ((chart x).coordinate 0))) = (chart x).coordinate 0
  y_normalized : ∀ x : C.left,
    ((((Scheme.Modules.pullback (chart x).source).map map) ≫ (chart x).canonical.hom).app ⊤)
      (((chart x).forms.inv.app ⊤)
        (differential (Over.mk ((chart x).node ≫ nodeProjection (chart x).ring (chart x).parameter))
          ⊤ ((chart x).coordinate 1))) = -(chart x).coordinate 1

variable [HasDerivedPushforwards.{0}]

/-- The source branch module arrow is the actual relative derivative followed by the nodal class. -/
def branchModuleMap {C Y T : Over (Spec (.of k))} {p : C ⟶ T} {q : Y ⟶ T}
    {f : C ⟶ Y} {over : f ≫ q = p} {D : RelativeFormsData C T p} {E : RelativeFormsData Y T q}
    (F : RelativeFormsMap f over D E) {ω : C.left.Modules} (G : NodalFundamentalClass D ω) :
    (Scheme.Modules.pullback f.left).obj (relativeForms E) ⟶ ω := F.map ≫ G.map

/-- The actual branch complex, with its two module terms in degrees [-1,0] and actual Rf_*. -/
def branchComplex {C Y T : Over (Spec (.of k))} {p : C ⟶ T} {q : Y ⟶ T}
    {f : C ⟶ Y} {over : f ≫ q = p} {D : RelativeFormsData C T p} {E : RelativeFormsData Y T q}
    (F : RelativeFormsMap f over D E) (P : ProperReference p.left)
    (G : NodalFundamentalClass D (properCanonicalModule P 1)) : FourierMukai.D Y.left :=
  (derivedPushforward f.left).obj (DerivedCategory.Q.obj (CochainComplex.mappingCone
    ((CochainComplex.singleFunctor C.left.Modules 0).map (branchModuleMap F G))))

end MathlibExt.AlgebraicGeometry.HurwitzBranchComplexes

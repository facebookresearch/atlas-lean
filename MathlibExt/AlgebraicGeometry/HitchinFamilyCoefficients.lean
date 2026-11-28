/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeometricHiggsFamilies
public import MathlibExt.AlgebraicGeometry.LineSectionScalars
public import MathlibExt.AlgebraicGeometry.IntegrableHiggsBundles
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# The actual Hitchin coefficient space and family map

The coefficient space is the affine scheme of the polynomial algebra on
bases of actual global sections of K^i. A family map is fixed by equating
every actual elementary characteristic section with its coordinate expansion.
This includes arbitrary parameter schemes, hence nonreduced tests. For rank2
these are trace and determinant, with spectral polynomial y^2-s1*y+s2.
No properness of the Hitchin map, spectral smoothness, NAH or P=W result
is assumed in the data. K^2 is tensor square, not exterior Omega2.

References: Hitchin, Stable bundles and integrable systems (1987), §4;
de Cataldo--Hausel--Migliorini, arXiv:1004.1420v2, (1.3.1)--(1.3.5).
The native scheme/module pullbacks are fixed here. AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b (Apache2.0),
StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/
BaseChangeCohomologyFlatExtension.lean, supplies completed normalized
derived ring comparisons; it is not identified here with the full native
proper global-section coefficient producer. That integration boundary is
kept explicit in the family map request.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.HitchinFamilyCoefficients
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.GeometricHiggsFamilies
open MathlibExt.AlgebraicGeometry.LineSectionScalars
open MathlibExt.AlgebraicGeometry.IntegrableHiggsBundles
open scoped BigOperators

/-- Actual finite bases of the coefficient-section spaces in every positive degree. -/
structure CoefficientChart (C : ComplexScheme) (r : ℕ) where
  cotangentLine : IsLineBundle (Omega C 1)
  dimension : Fin r → ℕ
  basis : ∀ i : Fin r, Module.Basis (Fin (dimension i)) ℂ
    ((sectionsFunctor C.hom).obj (power (Omega C 1) (i.val+1)))

abbrev Variables {C : ComplexScheme} {r : ℕ} (B : CoefficientChart C r) :=
  Sigma fun i : Fin r => Fin (B.dimension i)

abbrev coordinateRing {C : ComplexScheme} {r : ℕ} (B : CoefficientChart C r) :=
  MvPolynomial (Variables B) ℂ

def coefficientSpace {C : ComplexScheme} {r : ℕ} (B : CoefficientChart C r) : ComplexScheme :=
  Over.mk (Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℂ →+* coordinateRing B)))

/-- The actual coordinate regular function of an actual parameter map. -/
def coordinate {C T : ComplexScheme} {r : ℕ} {B : CoefficientChart C r}
    (m : T ⟶ coefficientSpace B) (v : Variables B) : Γ(T.left,⊤) :=
  pullFunction m.left ((Scheme.ΓSpecIso (.of (coordinateRing B))).inv (MvPolynomial.X v : coordinateRing B))

/-- Each coefficient basis vector is an actual structure-module arrow. -/
def basisSection {C : ComplexScheme} {r : ℕ} (B : CoefficientChart C r)
    (i : Fin r) (j : Fin (B.dimension i)) : Section (power (Omega C 1) (i.val+1)) :=
  fromTop (power (Omega C 1) (i.val+1)) (B.basis i j)

/-- Coordinate expansion as an actual section on the product family. -/
def expansion {C T : ComplexScheme} {r : ℕ} (B : CoefficientChart C r)
    (m : T ⟶ coefficientSpace B) (i : Fin r) :
    Section ((Scheme.Modules.pullback (prod.fst : prod C T ⟶ C).left).obj
      (power (Omega C 1) (i.val+1))) :=
  ∑ j : Fin (B.dimension i),
    scale (pullFunction (prod.snd : prod C T ⟶ T).left (coordinate m ⟨i,j⟩))
      (pullbackSection (prod.fst : prod C T ⟶ C).left (basisSection B i j))

/-- The map is characterized on all elementary characteristic sections.
The fixed pullback-power comparison removes the parenthesization ambiguity. -/
structure FamilyMap {C T : ComplexScheme} {r : ℕ} (B : CoefficientChart C r)
    (E : CurveFamily C T (Omega C 1) r) (K : CharacteristicSections E)
    (P : PullbackPowers (prod.fst : prod C T ⟶ C).left) where
  map : T ⟶ coefficientSpace B
  normalization : ∀ i : Fin r,
    K.coefficient (i.val+1) ≫ (P.comparison (i.val+1)).inv.app (Omega C 1) = expansion B map i

end MathlibExt.AlgebraicGeometry.HitchinFamilyCoefficients

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedSourceRelativeIsotropicMaps
public import MathlibExt.AlgebraicGeometry.DerivedFibreClosingPaths

/-!
# The native derived-intersection residue cochain, form and Theta

The loop is the original h+u(omega)-j-s0(f*omega). Its degree-one
coefficient is read by the native alternating projection, DK counit,
good truncation and exact shift. It is a closed NC cochain of degree
n-3, hence a closed two-form of degree n-1. A residue vertex must have
that exact cochain coefficient; it is not an arbitrary closing form.

The intersection adapter uses the native universal fibre path and the
same computed NC comparison. Its Theta applies the same source cochain
contraction to this residue vertex. Compatible vertex construction and
Lagrangian nondegeneracy are direct Wanted work.

Source: PTVV arXiv:1111.3209v4, Theorem 2.9 and its proof, pp.39--40.
Native DK, path, shift and public-source notices remain in imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedSourceResidueForms

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicTopology
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedStackFibreModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.DerivedIsotropicResidues
open MathlibExt.AlgebraicGeometry.DerivedLinearClosingPaths
open MathlibExt.AlgebraicGeometry.DerivedFibreClosingPaths
open MathlibExt.AlgebraicGeometry.DerivedNativeContractionSpaces
open MathlibExt.AlgebraicGeometry.DerivedCotangentFormSources
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open MathlibExt.Algebra.Homology.DoldKanNormalizedCoefficients
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k] {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {NC : NegativeCyclicDiagram D.functor (2 : ℤ)} {X : Prestack k}
    {F : GlobalNCModel D 2 NC X} {n : ℤ}

/-- The source residue is the literal normalized coefficient of h+u-j-s0(left), in NC degree n-3. -/
def residueNCcochain (P : ResiduePaths F n) : (ncComplex F).X (n - 3) :=
  (((ncComplex F).shiftFunctorObjXIso (n - 2) (-1) (n - 3) (by omega)).hom).hom
    ((coefficientMap ((ncComplex F)⟦n - 2⟧) 1).hom
      (show (simplicialModule ((ncComplex F)⟦n - 2⟧)) _⦋1⦌ from residueTerm P))

/-- The exact native loop coefficient is closed before any form representative is chosen. -/
theorem residueNCcochain_closed (P : ResiduePaths F n) :
    ((ncComplex F).d (n - 3) (n - 2)).hom (residueNCcochain P) = 0 := by
  let K := ncComplex F
  let t := n - 2
  let edge : (simplicialModule (K⟦t⟧)) _⦋1⦌ := residueTerm P
  let z := (coefficientMap (K⟦t⟧) 1).hom edge
  have hc : ((AlternatingFaceMapComplex.obj (simplicialModule (K⟦t⟧))).d 1 0).hom edge = 0 :=
    residueTerm_cycle P
  have hd := congrArg (fun f => f.hom edge) (coefficientMap_d (K⟦t⟧) 0)
  change ((K⟦t⟧).d (-1) 0).hom z = (coefficientMap (K⟦t⟧) 0).hom
    (((AlternatingFaceMapComplex.obj (simplicialModule (K⟦t⟧))).d 1 0).hom edge) at hd
  rw [hc, map_zero] at hd
  change t.negOnePow • (K.d (-1 + t) (0 + t)).hom z = 0 at hd
  have hd' := congrArg (fun a => t.negOnePow • a) hd
  simp only [smul_smul, Int.units_mul_self, one_smul, smul_zero] at hd'
  have hd'' := congrArg (fun a => ((K.XIsoOfEq (show 0 + t = n - 2 by omega)).hom).hom a) hd'
  have hcomp : (K.d (-1 + t) (0 + t) ≫
      (K.XIsoOfEq (show 0 + t = n - 2 by omega)).hom).hom z = 0 := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, map_zero] using hd''
  rw [K.d_comp_XIsoOfEq_hom] at hcomp
  have hs := congrArg (fun f => f.hom z)
    (K.XIsoOfEq_hom_comp_d (show -1 + t = n - 3 by omega) (n - 2))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hs
  exact hs.trans hcomp

/-- The native two-form degree n-1 has the literal NC shift n-3. -/
def residueVertexShift (F : GlobalNCModel D 2 NC X) (n : ℤ) :
    (ncComplex F)⟦(n - 1) - 2⟧ ⟶ (ncComplex F)⟦n - 3⟧ :=
  eqToHom (congrArg (fun i : ℤ => (ncComplex F)⟦i⟧) (by omega : (n - 1) - 2 = n - 3))

/-- The source residue vertex coefficient is compared through that same actual native shift. -/
def residueVertexCoefficient (F : GlobalNCModel D 2 NC X) (n : ℤ) (ω : ClosedForm F (n - 1)) :
    (ncComplex F).X (n - 3) :=
  vertexCoefficient (ncComplex F) (n - 3)
    (((realize k).map (residueVertexShift F n)).app (op ⦋0⦌) ω)

/-- A source residue form has the exact displayed loop cochain, not only an unspecified cohomology class. -/
structure ResidueClosedFormSource (P : ResiduePaths F n) where
  vertex : ClosedForm F (n - 1)
  normalized : residueVertexCoefficient F n vertex = residueNCcochain P

variable [Algebra ℚ k] {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {M : AffineModuleFibration N S} {U : RegularUnitSystem M} {R : RawModuleRealization M}
    {L : CochainLiftModel k}

/-- The residue Theta uses the same actual NC/eta/cap cochain contraction. -/
def residueTheta {Z : Prestack k}
    (SZ : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) Z)
    {n : ℤ} {P : ResiduePaths SZ.forms n} (V : ResidueClosedFormSource P) :
    DGHom (LargeScalar k) (n - 1) SZ.tangent.object SZ.context.cotangent.object :=
  sourceTheta SZ (n - 1) V.vertex

/-- Closure comes from that same source cochain/DK contraction. -/
theorem residueTheta_closed {Z : Prestack k}
    (SZ : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) Z)
    {n : ℤ} {P : ResiduePaths SZ.forms n} (V : ResidueClosedFormSource P) :
    dgDifferential (LargeScalar k) (n - 1) (residueTheta SZ V) = 0 :=
  sourceTheta_closed SZ (n - 1) V.vertex

/-- The native intersection form uses the original universal fibre path, with the coupled source NC models. -/
def intersectionResidueTheta {X Y T : DerivedStack Q} {P : NaturalPathModel T}
    {f : StackMap X T} {g : StackMap Y T} (Z : FibreStackModel P f g)
    (ST : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) T.functor)
    (SX : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) X.functor)
    (SY : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) Y.functor)
    (SZ : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) Z.stack.functor)
    (GP : GlobalNCModel D 2 NC P.P) (n : ℤ)
    (C : FibreNCPathModel Z ST.forms SX.forms SY.forms GP SZ.forms n)
    (ω : SourceClosedForm ST n)
    (J : LinearPath C.firstEndpoint C.secondEndpoint C.homotopy C.homotopy_d ω)
    (h : IsotropicPath SX.forms n ((closedPullback f ST.forms SX.forms n).app (op ⦋0⦌) ω))
    (j : IsotropicPath SY.forms n ((closedPullback g ST.forms SY.forms n).app (op ⦋0⦌) ω))
    (V : ResidueClosedFormSource (derivedResiduePaths C ω J h j)) :
    DGHom (LargeScalar k) (n - 1) SZ.tangent.object SZ.context.cotangent.object :=
  residueTheta SZ V

end MathlibExt.AlgebraicGeometry.DerivedSourceResidueForms

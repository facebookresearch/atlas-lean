/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedNormalizedGlobalExteriorComparison
public import MathlibExt.AlgebraicGeometry.DerivedIsotropicResidues
public import MathlibExt.Algebra.Homology.DoldKanNormalizedCoefficients

/-!
# Source-compatible NC space contraction and actual homotopy coefficients

Contraction is represented as a native cochain map. Its derived class is
the actual NC first projection, inverse of the computed global exterior
comparison, and native tensor/cap contraction. Good truncation and DK
then apply this same map to every closed-form simplex, including paths.

The degree-n vertex is read by the native normalized coefficient and
shift isomorphism. The degree-(n-1) path coefficient includes the native
(-1)^n shift sign. Its boundary is the actual target minus source.
Compatible cochain representatives are genuine source construction hooks;
an independently chosen closed Theta or isotropic h is not an input.

Sources: PTVV arXiv:1111.3209v4, Sections 1.2 and 2.2, Definitions
2.7--2.8; HAG II arXiv:math/0404373v7, Section 1.4.1. Native scalar,
DK, good truncation, shifts and DG source notices remain in imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedNativeContractionSpaces

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicTopology
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedCotangentDifferentials
open MathlibExt.AlgebraicGeometry.DerivedGlobalTensorModels
open MathlibExt.AlgebraicGeometry.DerivedMonoidalCoherenceModels
open MathlibExt.AlgebraicGeometry.DerivedSymplecticContractions
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.DerivedClosedFormContractionClasses
open MathlibExt.AlgebraicGeometry.DerivedCoherentExteriorDiagrams
open MathlibExt.AlgebraicGeometry.DerivedNormalizedGlobalExteriorComparison
open MathlibExt.AlgebraicGeometry.DerivedUniversalAffineSplittingMaps
open MathlibExt.AlgebraicGeometry.DerivedIsotropicResidues
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open MathlibExt.Algebra.Homology.DoldKanNormalizedCoefficients
open CochainComplex.HomComplex
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k]
attribute [local instance] HasDerivedCategory.standard

/-- Native inverse scalar transport keeps the original Hom complex and its coefficient universe. -/
def coefficientsToGlobal (k : Type u) [CommRing k] : Cochains (LargeScalar k) ⥤ GlobalComplex k :=
  (ModuleCat.restrictScalars (ULift.ringEquiv : LargeScalar k ≃+* k).symm.toRingHom).mapHomologicalComplex
    (.up ℤ)

/-- Transporting back changes neither the original native cochain nor its underlying value. -/
def coefficientRoundTripIso (K : Cochains (LargeScalar k)) :
    (globalToCoefficients k).obj ((coefficientsToGlobal k).obj K) ≅ K := Iso.refl _

/-- The genuine native Hom complex of the perfect tangent/cotangent pair, in the global coefficient category. -/
def homGlobal {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {M : AffineModuleFibration N S} {U : RegularUnitSystem M} {X : Prestack k}
    {G : QCohEnhancement M U X} (T L : G.category) : GlobalComplex k :=
  (coefficientsToGlobal k).obj (dgHomComplex (LargeScalar k) T L)

/-- A source closed vertex is the exact native normalized coefficient in degree n. -/
def vertexCoefficient (K : GlobalComplex k) (n : ℤ)
    (x : ((realize k).obj (K⟦n⟧)) _⦋0⦌) : K.X n :=
  ((K.shiftFunctorObjXIso n 0 n (by omega)).hom).hom
    ((coefficientMap (K⟦n⟧) 0).hom (show (simplicialModule (K⟦n⟧)) _⦋0⦌ from x))

/-- Its closure is inherited from the original good-truncation inclusion and native shift. -/
theorem vertexCoefficient_closed (K : GlobalComplex k) (n : ℤ)
    (x : ((realize k).obj (K⟦n⟧)) _⦋0⦌) :
    (K.d n (n + 1)).hom (vertexCoefficient K n x) = 0 := by
  let z := (coefficientMap (K⟦n⟧) 0).hom x
  have h : ((K⟦n⟧).d 0 1).hom z = 0 := by
    exact congrArg (fun f => f.hom x) (coefficientMap_zero_d (K⟦n⟧))
  change n.negOnePow • (K.d (0 + n) (1 + n)).hom z = 0 at h
  have h' := congrArg (fun t => n.negOnePow • t) h
  simp only [smul_smul, Int.units_mul_self, one_smul, smul_zero] at h'
  have h'' := congrArg (fun t =>
    ((K.XIsoOfEq (show 1 + n = n + 1 by omega)).hom).hom t) h'
  have h''' : (((K.d (0 + n) (1 + n)) ≫
      (K.XIsoOfEq (show 1 + n = n + 1 by omega)).hom).hom z) = 0 := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, map_zero] using h''
  rw [K.d_comp_XIsoOfEq_hom] at h'''
  dsimp only [vertexCoefficient, CochainComplex.shiftFunctorObjXIso]
  have hz := congrArg (fun f => f.hom z)
    (K.XIsoOfEq_hom_comp_d (show 0 + n = n by omega) (n + 1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hz
  exact hz.trans h'''

/-- The native degree-(n-1) path coefficient includes the actual (-1)^n target-shift sign. -/
def pathCoefficient (K : GlobalComplex k) (n : ℤ)
    {x y : ((realize k).obj (K⟦n⟧)) _⦋0⦌}
    (e : SSet.Edge (X := (realize k).obj (K⟦n⟧)) x y) : K.X (n - 1) :=
  n.negOnePow • ((K.shiftFunctorObjXIso n (-1) (n - 1) (by omega)).hom).hom
    ((coefficientMap (K⟦n⟧) 1).hom (show (simplicialModule (K⟦n⟧)) _⦋1⦌ from e.edge))

/-- The actual alternating differential of an edge is target minus source. -/
theorem alternatingEdge_boundary (K : GlobalComplex k)
    {x y : (simplicialModule K) _⦋0⦌} (e : SSet.Edge (X := (realize k).obj K) x y) :
    ((AlternatingFaceMapComplex.obj (simplicialModule K)).d 1 0).hom e.edge = y - x := by
  change (AlternatingFaceMapComplex.objD (simplicialModule K) 0).hom e.edge = y - x
  change (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (simplicialModule K).δ i).hom e.edge = y - x
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
    ModuleCat.hom_add, ModuleCat.hom_neg, LinearMap.add_apply, LinearMap.neg_apply]
  have hs : ((simplicialModule K).δ 1).hom e.edge = x := e.src_eq
  have ht : ((simplicialModule K).δ 0).hom e.edge = y := e.tgt_eq
  rw [hs, ht]
  exact (sub_eq_add_neg y x).symm

/-- The path boundary is the exact target/source vertex difference through the same normalized coefficient map. -/
theorem pathCoefficient_boundary (K : GlobalComplex k) (n : ℤ)
    {x y : ((realize k).obj (K⟦n⟧)) _⦋0⦌}
    (e : SSet.Edge (X := (realize k).obj (K⟦n⟧)) x y) :
    (K.d (n - 1) n).hom (pathCoefficient K n e) =
      vertexCoefficient K n y - vertexCoefficient K n x := by
  let edge : (simplicialModule (K⟦n⟧)) _⦋1⦌ := e.edge
  have h := congrArg (fun f => f.hom edge) (coefficientMap_d (K⟦n⟧) 0)
  change ((K⟦n⟧).d (-1) 0).hom ((coefficientMap (K⟦n⟧) 1).hom edge) =
    (coefficientMap (K⟦n⟧) 0).hom
      (((AlternatingFaceMapComplex.obj (simplicialModule (K⟦n⟧))).d 1 0).hom edge) at h
  have hb := alternatingEdge_boundary (K⟦n⟧) e
  change (((AlternatingFaceMapComplex.obj (simplicialModule (K⟦n⟧))).d 1 0).hom edge) =
    (show (simplicialModule (K⟦n⟧)) _⦋0⦌ from y) -
      (show (simplicialModule (K⟦n⟧)) _⦋0⦌ from x) at hb
  rw [hb, map_sub] at h
  change n.negOnePow • (K.d (-1 + n) (0 + n)).hom
    ((coefficientMap (K⟦n⟧) 1).hom edge) = _ at h
  have h' := congrArg (fun z =>
    ((K.XIsoOfEq (show 0 + n = n by omega)).hom).hom z) h
  simp only [map_zsmul_unit, map_sub] at h'
  have ht := congrArg (fun f => f.hom ((coefficientMap (K⟦n⟧) 1).hom edge))
    (K.d_comp_XIsoOfEq_hom (show 0 + n = n by omega) (-1 + n))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at ht
  rw [ht] at h'
  have hs := congrArg (fun f => f.hom ((coefficientMap (K⟦n⟧) 1).hom edge))
    (K.XIsoOfEq_hom_comp_d (show -1 + n = n - 1 by omega) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hs
  change (K.d (n - 1) n).hom
    (n.negOnePow • ((K.shiftFunctorObjXIso n (-1) (n - 1) (by omega)).hom).hom
      ((coefficientMap (K⟦n⟧) 1).hom edge)) = _
  rw [map_zsmul_unit]
  exact (congrArg (fun z => n.negOnePow • z) hs).trans h'

variable [Algebra ℚ k] {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {NC : NegativeCyclicDiagram D.functor (2 : ℤ)} {N : ShuffleAlgebraFunctor k}
    {S : AffineScalarSystem N} {M : AffineModuleFibration N S} {U : RegularUnitSystem M}
    {R : RawModuleRealization M} {L : CochainLiftModel k} {X : Prestack k}
    {G : QCohEnhancement M U X} {C : CotangentContext R G}
    {H : CoherentMonoidalEnhancement G} {E : ExteriorSquare H C.cotangent.object}
    {B : UniversalExteriorFamilies D L X G C H E} {Cone : CoherentExteriorCone B}
    {F : GlobalNCModel D 2 NC X} {P : GlobalNCModel D 2 NC (affineParameterPrestack Q X)}
    [PreservesLimit P.ordinary.diagram (coefficientWeightFunctor k)]
    [QuasiIso (coefficientWeightPullback (affineParameterPoint Q X) F P)]
    (η : GlobalExteriorRepresentative Cone F P) [QuasiIso η.map]
    (T : PerfectDual H.monoidal C.cotangent.object)

/-- The source cochain contraction represents the literal NC/eta-inverse/cap composite. -/
structure NCContractionSource where
  map : (ncComplex F)⟦-2⟧ ⟶ homGlobal T.object C.cotangent.object
  normalized : DerivedCategory.Q.map ((globalToCoefficients k).map map) ≫
    DerivedCategory.Q.map (coefficientRoundTripIso (dgHomComplex (LargeScalar k)
      T.object C.cotangent.object)).hom =
    DerivedCategory.Q.map ((shiftFunctor (Cochains (LargeScalar k)) (-2)).map
      ((globalToCoefficients k).map (projection F))) ≫ inv (DerivedCategory.Q.map η.map) ≫
      DerivedCategory.Q.map (contractionMap H E T)

/-- Every closing-data simplex uses the same source contraction cochain and native shift composition. -/
def contractionSpace (A : NCContractionSource η T) (n : ℤ) :
    closedSpace F n ⟶ (realize k).obj ((homGlobal T.object C.cotangent.object)⟦n⟧) :=
  (realize k).map
    ((shiftFunctorAdd' (GlobalComplex k) (-2 : ℤ) n (n - 2) (by omega)).hom.app (ncComplex F) ≫
      (shiftFunctor (GlobalComplex k) n).map A.map)

/-- Theta is the literal native coefficient of the same contracted closed-form simplex. -/
def theta (A : NCContractionSource η T) (n : ℤ) (ω : ClosedForm F n) :
    DGHom (LargeScalar k) n T.object C.cotangent.object :=
  vertexCoefficient (homGlobal T.object C.cotangent.object) n
    ((contractionSpace η T A n).app (op ⦋0⦌) ω)

/-- Closure follows from the actual normalized vertex coefficient, not a selected cohomology representative. -/
theorem theta_closed (A : NCContractionSource η T) (n : ℤ) (ω : ClosedForm F n) :
    dgDifferential (LargeScalar k) n (theta η T A n ω) = 0 := by
  exact vertexCoefficient_closed (homGlobal T.object C.cotangent.object) n
    ((contractionSpace η T A n).app (op ⦋0⦌) ω)

/-- Native space contraction preserves the actual zero closed form. -/
theorem contractionSpace_zero (A : NCContractionSource η T) (n : ℤ) :
    (contractionSpace η T A n).app (op ⦋0⦌) (zeroForm F n) =
      (0 : (simplicialModule ((homGlobal T.object C.cotangent.object)⟦n⟧)) _⦋0⦌) :=
  realize_map_zero _

/-- The actual isotropic homotopy is the degree-(n-1) coefficient of its image under that same source map. -/
def isotropicHomotopy (A : NCContractionSource η T) (n : ℤ) (ω : ClosedForm F n)
    (h : IsotropicPath F n ω) : DGHom (LargeScalar k) (n - 1) T.object C.cotangent.object :=
  pathCoefficient (homGlobal T.object C.cotangent.object) n
    (h.map (contractionSpace η T A n))

/-- Its boundary is the same actual Theta of the path's source closed form. -/
theorem isotropicHomotopy_boundary (A : NCContractionSource η T) (n : ℤ) (ω : ClosedForm F n)
    (h : IsotropicPath F n ω) :
    ((dgHomComplex (LargeScalar k) T.object C.cotangent.object).d (n - 1) n).hom
      (isotropicHomotopy η T A n ω h) = theta η T A n ω := by
  have hb := pathCoefficient_boundary (homGlobal T.object C.cotangent.object) n
    (h.map (contractionSpace η T A n))
  have hz : vertexCoefficient (homGlobal T.object C.cotangent.object) n
      ((contractionSpace η T A n).app (op ⦋0⦌) (zeroForm F n)) = 0 := by
    rw [contractionSpace_zero]
    unfold vertexCoefficient
    rw [map_zero, map_zero]
  rw [hz, sub_zero] at hb
  exact hb

/-- Symplectic nondegeneracy tests the same source-compatible Theta on every native representable Hom. -/
def IsSymplectic (A : NCContractionSource η T) (n : ℤ) (ω : ClosedForm F n) : Prop :=
  IsShiftedEquivalence C.cotangent.object T.object n (theta η T A n ω)
    (theta_closed η T A n ω)

end MathlibExt.AlgebraicGeometry.DerivedNativeContractionSpaces

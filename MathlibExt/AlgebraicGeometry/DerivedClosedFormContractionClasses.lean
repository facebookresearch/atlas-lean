/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedSymplecticContractions
public import MathlibExt.AlgebraicGeometry.DerivedClosedFormTransgression
public import MathlibExt.Algebra.Homology.DoldKanNormalizedCoefficients
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Literal NC projection and the native contraction class

The closed-form class is obtained from the original normalized
Dold--Kan coefficient, good-truncation inclusion and native shift.
The underlying form applies the actual NC first-coefficient projection.
Given the supplied source global exterior/de Rham comparison, its
inverse is taken on native homology, and contraction is the existing
tensor/cap composite with twice the exterior inclusion and its Koszul
transpose. Only a closed representative of that fixed class is chosen.

Source-normalized construction of the global exterior/de Rham map is
separate. This file computes its exact use; it does not supply an
arbitrary chart cotangent identification or a symplectic conclusion.

References: PTVV1111.3209v4, Sections1.1/1.2/2.2; native Dold--Kan,
good truncation, shifts and tensor/contraction notices remain in imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedClosedFormContractionClasses

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.DerivedClosedFormTransgression
open MathlibExt.AlgebraicGeometry.DerivedMonoidalCoherenceModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalTensorModels
open MathlibExt.AlgebraicGeometry.DerivedSymplecticContractions
open MathlibExt.Algebra.Homology.DoldKanNormalizedCoefficients
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open scoped Simplicial

universe u v w

/-- The native degree-zero normalized coefficient lands in the original good-truncation cycles. -/
theorem coefficientMap_zero_d {C : Type v} [Category.{w} C] [Abelian C]
    (K : CochainComplex C ℤ) :
    MathlibExt.Algebra.Homology.DoldKanNormalizedCoefficients.coefficientMap K 0 ≫ K.d 0 1 = 0 := by
  dsimp only [MathlibExt.Algebra.Homology.DoldKanNormalizedCoefficients.coefficientMap]
  have h : K.truncLE'ToX 0 ≫ K.d 0 1 = 0 := by
    have h₀ := K.truncLE'ToX_zero_d 1
    exact h₀
  rw [Category.assoc, h, comp_zero]

/-- A literal coefficient cycle gives its native homology class through the original cycle inclusion/quotient. -/
def cycleClass {R : Type u} [CommRing R] (K : Cochains R) (n : ℤ)
    (z : K.X n) (hz : (K.d n (n + 1)).hom z = 0) : K.homology n := by
  let a : ModuleCat.of R R ⟶ K.X n := ModuleCat.ofHom (LinearMap.toSpanSingleton R _ z)
  have ha : a ≫ K.d n (n + 1) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change (K.d n (n + 1)).hom (r • z) = 0
    rw [map_smul, hz, smul_zero]
  exact (K.liftCycles a (n + 1) ((ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel n (n + 1) by simp))
    ha ≫ K.homologyπ n) (1 : R)

variable {k : Type u} [CommRing k] {Q : AlgebraReplacementFunctor k}
  {D : AffineDRSystem Q} {NC : NegativeCyclicDiagram D.functor (2 : ℤ)} {X : Prestack k}
  (F : GlobalNCModel D 2 NC X)

/-- The actual coefficient NC complex, retaining its original full closing data. -/
def coefficientNC : Cochains (LargeScalar k) := (globalToCoefficients k).obj (ncComplex F)

/-- Its source closed-form vertex gives the literal native shifted degree-zero homology class. -/
def shiftedNCVertexClass (n : ℤ) (ω : ClosedForm F n) :
    ((coefficientNC F)⟦n - 2⟧).homology 0 := by
  let K := (ncComplex F)⟦n - 2⟧
  let z : ((coefficientNC F)⟦n - 2⟧).X 0 :=
    (MathlibExt.Algebra.Homology.DoldKanNormalizedCoefficients.coefficientMap K 0).hom ω
  have hz : (((coefficientNC F)⟦n - 2⟧).d 0 1).hom z = 0 := by
    have h := congrArg (fun a => a.hom ω) (coefficientMap_zero_d K)
    exact h
  exact cycleClass ((coefficientNC F)⟦n - 2⟧) 0 z hz

/-- The closed-form NC class has degree n-2, through the same actual native shift comparison. -/
def ncVertexClass (n : ℤ) (ω : ClosedForm F n) : (coefficientNC F).homology (n - 2) :=
  (((HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} (LargeScalar k)) (.up ℤ) 0).shiftIso
    (n - 2) 0 (n - 2) (by omega)).app (coefficientNC F)).hom (shiftedNCVertexClass F n ω)

variable [Algebra ℚ k] {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
  {M : AffineModuleFibration N S} {U : RegularUnitSystem M} (G : QCohEnhancement M U X)
  (H : CoherentMonoidalEnhancement G) (L : G.category) (E : ExteriorSquare H L)
  (T : PerfectDual H.monoidal L)
  (η : globalHom G E.object ⟶ ((globalToCoefficients k).obj (weightComplex F))⟦-2⟧)
  [QuasiIso η]

/-- The actual first-coefficient projection and weight shift give the underlying global exterior class. -/
def exteriorClass (n : ℤ) (ω : ClosedForm F n) : (globalHom G E.object).homology n := by
  let W := (globalToCoefficients k).obj (weightComplex F)
  let p := (globalToCoefficients k).map (projection F)
  let c := (HomologicalComplex.homologyMap p (n - 2)).hom (ncVertexClass F n ω)
  let s := ((HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} (LargeScalar k)) (.up ℤ) 0).shiftIso
    (-2) n (n - 2) (by omega)).app W
  letI : IsIso (HomologicalComplex.homologyMap η n) :=
    (quasiIsoAt_iff_isIso_homologyMap η n).mp (by infer_instance)
  exact (asIso (HomologicalComplex.homologyMap η n)).inv (s.inv c)

/-- Theta is the actual native tensor/cap contraction of this fixed exterior class. -/
def contractionClass (n : ℤ) (ω : ClosedForm F n) :
    (dgHomComplex (LargeScalar k) T.object L).homology n :=
  (HomologicalComplex.homologyMap (contractionMap H E T) n).hom
    (exteriorClass F G H L E η n ω)

/-- A representative is chosen only from the actual native homology projection. -/
def homologyCycleRepresentative {R : Type u} [CommRing R] (K : Cochains R) (n : ℤ)
    (c : K.homology n) : K.cycles n :=
  Classical.choose (((ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance) c)

/-- Its quotient is exactly the prescribed original homology class. -/
theorem homologyCycleRepresentative_class {R : Type u} [CommRing R] (K : Cochains R) (n : ℤ)
    (c : K.homology n) : (K.homologyπ n).hom (homologyCycleRepresentative K n c) = c :=
  Classical.choose_spec (((ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance) c)

/-- The chosen homogeneous value comes through the actual native cycle inclusion. -/
def homologyCochainRepresentative {R : Type u} [CommRing R] (K : Cochains R) (n : ℤ)
    (c : K.homology n) : K.X n :=
  (K.iCycles n).hom (homologyCycleRepresentative K n c)

/-- For a commutative ring $R$, a cochain complex $K$ of $R$-modules indexed by $\mathbb{Z}$, an
integer $n$ and a class $c \in H^n(K)$, the chosen representative
`homologyCochainRepresentative K n c` of $c$ in $K^n$ is a cocycle: the differential
$K^n \to K^{n+1}$ sends it to $0$. -/
theorem homologyCochainRepresentative_closed {R : Type u} [CommRing R] (K : Cochains R) (n : ℤ)
    (c : K.homology n) : (K.d n (n + 1)).hom (homologyCochainRepresentative K n c) = 0 := by
  exact congrArg (fun a => a.hom (homologyCycleRepresentative K n c)) (K.iCycles_d n (n + 1))

/-- Theta is a closed representative of the literal NC/exterior/cap contraction class, in the source degree n. -/
def theta (n : ℤ) (ω : ClosedForm F n) : DGHom (LargeScalar k) n T.object L :=
  homologyCochainRepresentative (dgHomComplex (LargeScalar k) T.object L) n
    (contractionClass F G H L E T η n ω)

/-- The source degree-n Theta arrow is genuinely closed. -/
theorem theta_closed (n : ℤ) (ω : ClosedForm F n) :
    dgDifferential (LargeScalar k) n (theta F G H L E T η n ω) = 0 := by
  simpa only [theta, dgDifferential_linearHomComplex] using
    homologyCochainRepresentative_closed (dgHomComplex (LargeScalar k) T.object L) n
      (contractionClass F G H L E T η n ω)

/-- Symplectic nondegeneracy tests this same fixed source-normalized closed arrow on every represented tangent Hom. -/
def IsSymplecticForm (n : ℤ) (ω : ClosedForm F n) : Prop :=
  IsShiftedEquivalence L T.object n (theta F G H L E T η n ω)
    (theta_closed F G H L E T η n ω)

end MathlibExt.AlgebraicGeometry.DerivedClosedFormContractionClasses

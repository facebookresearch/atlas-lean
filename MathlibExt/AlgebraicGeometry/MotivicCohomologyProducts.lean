/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicTensorOperations

/-!
# Native reduced-chain Alexander--Whitney and motivic cups

The reduced-free smash map is fixed on every actual product simplex.
Normalized Alexander--Whitney uses Mathlib's comparison to the actual
idempotent summand and the imported inclusion/projection source maps.
Negative extension gives the literal source chain map. Derived external
cup is then the canonical tensor comparison, the two input derived Homs,
native shifted tensor and the fixed coefficient cycle multiplication.
Cup is its pullback along the native pointed diagonal.

No arbitrary cohomology isomorphism, cup operation or ring law is supplied.
Ordinary free-chain/tensor comparison proofs and cup laws remain separate
construction/theorem requests.

Sources: Voevodsky arXiv:math/0107109v1, equations 2.1--2.4 and Theorem
2.2, pp. 3--5; Mazza--Voevodsky--Weibel, Constructions 3.10--3.11.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicCohomologyProducts

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open FiniteTransferCycleModels FiniteTransferProductModels
open NisnevichTransferModels MotivicStandardSchemes
open EffectiveMotivicComplexModels PointedMotivicModels
open ReducedMotivicCohomologyModels MotivicRealizationComparisons
open MotivicCycleProducts MotivicTensorOperations PointedMotivicQuotients
open MathlibExt.SpectraSource
open scoped Simplicial ZeroObject

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  (N : NisTensorSystem k) [N.functor.Additive]
  [∀ H, (N.functor.obj H).Additive]

/-- Inclusion of native normalized Moore chains into the alternating
complex through the actual Dold--Kan idempotent summand. -/
def mooreInclusion (F : SimplicialObject (NisModules (k := k))) :
    (AlgebraicTopology.normalizedMooreComplex _).obj F ⟶ alternatingChains F :=
  (Abelian.DoldKan.comparisonN.app F).hom ≫ Idempotents.DoldKan.inclusionN.app F

/-- The native projection onto normalized Moore chains. -/
def mooreProjection (F : SimplicialObject (NisModules (k := k))) :
    alternatingChains F ⟶ (AlgebraicTopology.normalizedMooreComplex _).obj F :=
  Idempotents.DoldKan.PInftyToN.app F ≫ (Abelian.DoldKan.comparisonN.app F).inv

/-- The actual normalized Alexander--Whitney chain map. -/
def normalizedAlexanderWhitney (Z : EilenbergZilberModel N)
    (F H : SimplicialObject (NisModules (k := k))) :
    (AlgebraicTopology.normalizedMooreComplex _).obj (simplicialTensor N F H) ⟶
      chainTensor N ((AlgebraicTopology.normalizedMooreComplex _).obj F)
        ((AlgebraicTopology.normalizedMooreComplex _).obj H) :=
  mooreInclusion (simplicialTensor N F H) ≫ Z.alexanderWhitney F H ≫
    HomologicalComplex.mapBifunctorMap (mooreProjection F) (mooreProjection H)
      N.functor (ComplexShape.down ℕ)

/-- A generator enters the actual reduced-free sheaf by its own unit. -/
def reducedGenerator (F : ReducedFreeNisSystem k) (X : PointedSpaces (k := k))
    (n : SimplexCategoryᵒᵖ) (U : (SmoothScheme k)ᵒᵖ)
    (t : ((𝟙_ (Spaces (k := k))).obj U).obj n) (x : (X.right.obj U).obj n) :
    (((reducedSimplicialFunctor F).obj X).obj n).obj.obj U :=
  (((sheafificationAdjunction (nisnevichTopology (k := k))
    (ModuleCat.{1} ℤ)).unit.app ((F.functor.obj X).obj n)).app U)
      ((F.valueIso X n U t).inv (ReducedFreeModule.mk ℤ x))

/-- An actual product simplex obtained by the native product universal
property, with the evaluation-product comparison explicitly retained. -/
def productSimplex (X Y : PointedSpaces (k := k))
    (n : SimplexCategoryᵒᵖ) (U : (SmoothScheme k)ᵒᵖ)
    (x : (X.right.obj U).obj n) (y : (Y.right.obj U).obj n) :
    ((prod X.right Y.right).obj U).obj n :=
  SSet.yonedaEquiv
    (prod.lift (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y) ≫
      (asIso (prodComparison ((evaluation (SmoothScheme k)ᵒᵖ SSet.{1}).obj U)
        X.right Y.right)).inv)

/-- The generator formula fixing a reduced-free smash comultiplication: the generator of a
product simplex goes to the tensor of the generators of its two factors. -/
def IsComultiplicationNormalized (F : ReducedFreeNisSystem k)
    (map : ∀ X Y : PointedSpaces (k := k),
      (reducedSimplicialFunctor F).obj (smash X Y) ⟶
        simplicialTensor N ((reducedSimplicialFunctor F).obj X)
          ((reducedSimplicialFunctor F).obj Y)) : Prop :=
  ∀ (X Y : PointedSpaces (k := k)) (n : SimplexCategoryᵒᵖ)
    (U : (SmoothScheme k)ᵒᵖ) (t : ((𝟙_ (Spaces (k := k))).obj U).obj n)
    (x : (X.right.obj U).obj n) (y : (Y.right.obj U).obj n),
    (((map X Y).app n).hom.app U)
      (reducedGenerator F (smash X Y) n U t
        ((((smashQuotient X Y).app U).app n) (productSimplex X Y n U x y))) =
      tensorElement N _ _ U (reducedGenerator F X n U t x)
        (reducedGenerator F Y n U t y)

/-- Reduced-free smash comultiplication is fixed on all product generators,
including generators on either collapsed basepoint axis. -/
structure ReducedSmashComultiplication (F : ReducedFreeNisSystem k) where
  map : ∀ X Y : PointedSpaces (k := k),
    (reducedSimplicialFunctor F).obj (smash X Y) ⟶
      simplicialTensor N ((reducedSimplicialFunctor F).obj X)
        ((reducedSimplicialFunctor F).obj Y)
  generator : IsComultiplicationNormalized N F map

/-- The literal reduced source smash chain map: normalized Moore,
Alexander--Whitney, negative extension and its fixed tensor comparison. -/
def reducedSmashMap (F : ReducedFreeNisSystem k)
    (M : ReducedSmashComultiplication N F) (Z : EilenbergZilberModel N)
    (V : NegativeTensorComparison N) (X Y : PointedSpaces (k := k)) :
    (reducedComplexFunctor F).obj (smash X Y) ⟶
      cochainTensor N ((reducedComplexFunctor F).obj X)
        ((reducedComplexFunctor F).obj Y) :=
  (negativeEmbedding.extendFunctor (NisModules (k := k))).map
    ((AlgebraicTopology.normalizedMooreComplex _).map (M.map X Y) ≫
      normalizedAlexanderWhitney N Z ((reducedSimplicialFunctor F).obj X)
        ((reducedSimplicialFunctor F).obj Y)) ≫
    (V.iso ((AlgebraicTopology.normalizedMooreComplex _).obj
      ((reducedSimplicialFunctor F).obj X))
      ((AlgebraicTopology.normalizedMooreComplex _).obj
        ((reducedSimplicialFunctor F).obj Y))).inv

attribute [local instance] HasDerivedCategory.standard

/-- The actual bifunctor map on two derived morphisms. -/
def derivedTensorMap (F : KFlatResolutionSystem N) (D : DerivedTensorSource N F)
    {X X' Y Y' : DerivedCategory (NisModules (k := k))}
    (a : X ⟶ X') (b : Y ⟶ Y') :
    (D.functor.obj X).obj Y ⟶ (D.functor.obj X').obj Y' :=
  (D.functor.map a).app Y ≫ (D.functor.obj X').map b

/-- The normalization of derived tensor shift isomorphisms by the cochain tensor shift and
the native `Q`/shift comparison maps. -/
def IsShiftNormalized (F : KFlatResolutionSystem N) (D : DerivedTensorSource N F)
    (iso : ∀ (X Y : DerivedCategory (NisModules (k := k))) (p r : ℤ),
      (D.functor.obj (X⟦p⟧)).obj (Y⟦r⟧) ≅ ((D.functor.obj X).obj Y)⟦p + r⟧) : Prop :=
  ∀ (X Y : CochainComplex (NisModules (k := k)) ℤ) (p r : ℤ),
    (iso (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj Y) p r).hom ≫
      (tensorComparison N F D X Y)⟦p + r⟧' =
    derivedTensorMap N F D ((DerivedCategory.Q.commShiftIso p).inv.app X)
      ((DerivedCategory.Q.commShiftIso r).inv.app Y) ≫
      tensorComparison N F D (X⟦p⟧) (Y⟦r⟧) ≫
      DerivedCategory.Q.map (tensorShiftIso N X Y p r).hom ≫
      (DerivedCategory.Q.commShiftIso (p + r)).hom.app (cochainTensor N X Y)

/-- Shifted derived tensor is normalized by the actual cochain tensor
shift and both native Q/shift comparison maps, for all complexes. -/
structure DerivedTensorShifts (F : KFlatResolutionSystem N)
    (D : DerivedTensorSource N F) where
  iso : ∀ (X Y : DerivedCategory (NisModules (k := k))) (p r : ℤ),
    (D.functor.obj (X⟦p⟧)).obj (Y⟦r⟧) ≅ ((D.functor.obj X).obj Y)⟦p + r⟧
  normalization : IsShiftNormalized N F D iso

/-- The ordinary tensor comparison on free reduced source complexes is
the *canonical augmentation map*. Its invertibility is a proof request,
and is separate from any motivic cup or representability law. -/
def IsFreeTensorComparison (F : KFlatResolutionSystem N)
    (D : DerivedTensorSource N F) (R₁ : ReducedFreeNisSystem k) : Prop :=
  ∀ X Y : PointedSpaces (k := k), IsIso
    (tensorComparison N F D ((reducedComplexFunctor R₁).obj X)
      ((reducedComplexFunctor R₁).obj Y))

variable {D₀ : CompositionSystem k} {G : GraphSystem k}
  [CorrespondenceLaws D₀ G] [CorrespondenceAdditivity D₀ G]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D₀ G P E} {A : StandardSchemes P}
  {R : RepresentableSystem D₀ G} {S : TransferSheafificationModel D₀ G}
  {T : CycleComplexSystem (D := D₀) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R)}
  (B : CoefficientComplexSystem (D := D₀) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R) (S := S) T N)
  {J : TorusConcatenation A}
  {M₀ : SingularCycleProduct (S := S) N T J} {Z : EilenbergZilberModel N}
  {V : NegativeTensorComparison N}
  (L : CoefficientMultiplicationSystem N T B M₀ Z V)
  (F : KFlatResolutionSystem N) (D : DerivedTensorSource N F)
  (H : DerivedTensorShifts N F D) (R₁ : ReducedFreeNisSystem k)
  (M : ReducedSmashComultiplication N R₁)

/-- External cup on the actual derived groups, for any specified bilinear
coefficient map. Its only inverse is the fixed free-source tensor augmentation. -/
def externalCup (hF : IsFreeTensorComparison N F D R₁)
    (X Y : PointedSpaces (k := k)) (p q r s : ℤ)
    (A₁ A₂ A₃ : ModuleCat.{1} ℤ) (μ : TensorProduct ℤ A₁ A₂ →ₗ[ℤ] A₃)
    (u : ReducedCohomology B R₁ X p q A₁)
    (v : ReducedCohomology B R₁ Y r s A₂) :
    ReducedCohomology B R₁ (smash X Y) (p + r) (q + s) A₃ := by
  letI := hF X Y
  exact DerivedCategory.Q.map (reducedSmashMap N R₁ M Z V X Y) ≫
    (asIso (tensorComparison N F D ((reducedComplexFunctor R₁).obj X)
      ((reducedComplexFunctor R₁).obj Y))).inv ≫
    derivedTensorMap N F D u v ≫
    (H.iso (DerivedCategory.Q.obj ((B.weightFunctor q).obj A₁))
      (DerivedCategory.Q.obj ((B.weightFunctor s).obj A₂)) p r).hom ≫
    (derivedCoefficientMultiplication N T B L F D A₁ A₂ A₃ μ q s)⟦p + r⟧'

/-- Cup is the actual pullback of external cup along the pointed diagonal. -/
def cup (hF : IsFreeTensorComparison N F D R₁)
    (X : PointedSpaces (k := k)) (p q r s : ℤ)
    (A₁ A₂ A₃ : ModuleCat.{1} ℤ) (μ : TensorProduct ℤ A₁ A₂ →ₗ[ℤ] A₃)
    (u : ReducedCohomology B R₁ X p q A₁)
    (v : ReducedCohomology B R₁ X r s A₂) :
    ReducedCohomology B R₁ X (p + r) (q + s) A₃ :=
  ReducedMotivicCohomologyModels.pullback B R₁ (smashDiagonal X)
    (p + r) (q + s) A₃ (externalCup N B L F D H R₁ M hF X X p q r s A₁ A₂ A₃ μ u v)

/-- The actual bilinear multiplication of a commutative coefficient ring. -/
def ringCoefficientMultiplication (R₂ : Type 1) [CommRing R₂] :
    TensorProduct ℤ R₂ R₂ →ₗ[ℤ] R₂ := LinearMap.mul' ℤ R₂

/-- Cup with the actual ring multiplication on coefficients. -/
def cupRing (hF : IsFreeTensorComparison N F D R₁)
    (R₂ : Type 1) [CommRing R₂] (X : PointedSpaces (k := k)) (p q r s : ℤ)
    (u : ReducedCohomology B R₁ X p q (ModuleCat.of ℤ R₂))
    (v : ReducedCohomology B R₁ X r s (ModuleCat.of ℤ R₂)) :
    ReducedCohomology B R₁ X (p + r) (q + s) (ModuleCat.of ℤ R₂) :=
  cup N B L F D H R₁ M hF X p q r s _ _ _ (ringCoefficientMultiplication R₂) u v

/-- Canonical transport along equal integer bidegrees. -/
def regrade (X : PointedSpaces (k := k)) (V₁ : ModuleCat.{1} ℤ)
    {p q p' q' : ℤ} (hp : p = p') (hq : q = q')
    (u : ReducedCohomology B R₁ X p q V₁) : ReducedCohomology B R₁ X p' q' V₁ := by
  subst p'
  subst q'
  exact u

/-- Smooth-scheme cohomology pullback is native precomposition by the
free Nisnevich representable map, on the published hypercohomology carrier. -/
def schemePullback {X Y : SmoothScheme k} (a : X ⟶ Y) (p q : ℤ)
    (V₁ : ModuleCat.{1} ℤ) :
    MotivicCohomology (D := D₀) (G := G) (P := P) (E := E)
      (C := C) (A := A) (R := R) (S := S) B Y p q V₁ →
    MotivicCohomology (D := D₀) (G := G) (P := P) (E := E)
      (C := C) (A := A) (R := R) (S := S) B X p q V₁ :=
  fun u => (DerivedCategory.singleFunctor (NisModules (k := k)) 0).map
    ((freeNisRepresentableFunctor (k := k)).map a) ≫ u

end MathlibExt.AlgebraicGeometry.MotivicCohomologyProducts

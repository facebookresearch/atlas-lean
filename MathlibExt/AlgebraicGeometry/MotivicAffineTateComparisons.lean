/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicAffineQuotientModels
public import MathlibExt.AlgebraicGeometry.MotivicPointedProducts
public import MathlibExt.AlgebraicGeometry.MotivicTateThomModels

/-!
# Fixed affine-cycle/Tate comparison map types and finite cycle realization

The affine Thom section is fixed by the actual diagonal finite cycle and
the actual quotient map. Comparison targets use the literal K(2q,q,A)
formed from the independently defined reduced-torus coefficient complex.
Coefficient and multiplicative comparisons are actual maps in the pointed
A1 localization. Rank one is fixed by the native relative cofiber boundary
of the graph torus class, so an arbitrary sign change is not the source
normalization. All weak-equivalence/existence conclusions are separate
direct Wanted construction targets, not inputs defining cohomology.

Source: Voevodsky arXiv:math/0107109v1, Section2/Theorem2.1, pp3–4;
Section4/Lemma4.2; Mazza--Voevodsky--Weibel, Lectures3/14.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicAffineTateComparisons

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open FiniteTransferCycleModels FiniteTransferProductModels
open NisnevichTransferModels MotivicStandardSchemes
open EffectiveMotivicComplexModels PointedMotivicModels
open ReducedMotivicCohomologyModels MotivicEilenbergMacLaneModels
open MotivicRealizationComparisons MotivicCycleProducts MotivicTensorOperations
open MotivicCohomologyProducts PointedMotivicQuotients
open MotivicAffineQuotientModels MotivicPointedProducts
open MotivicTorusClassModels MotivicTateThomModels MotivicBundleModels

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  {D₀ : CompositionSystem k} {G : GraphSystem k}
  [CorrespondenceLaws D₀ G] [CorrespondenceAdditivity D₀ G]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D₀ G P E} {A : StandardSchemes P}
  {R : RepresentableSystem D₀ G} {S : TransferSheafificationModel D₀ G}
  {T : CycleComplexSystem (D := D₀) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R)}
  (N : NisTensorSystem k) [N.functor.Additive] [∀ H, (N.functor.obj H).Additive]
  (B : CoefficientComplexSystem (D := D₀) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R) (S := S) T N)
  (I : KInjectiveResolutionSystem k) (Q : PointedSimplicialModuleFunctor k)
  (F : ReducedFreeNisSystem k) (J : ReducedFreeAdjunction F Q)
  (M : ModuleSectionSystem Q)

/-- The canonical affine Thom cycle section is the actual diagonal graph
cycle on affine space descended along its literal pointed open quotient. -/
structure AffineThomCycleSections where
  map : ∀ (q : ℕ) (V : ModuleCat.{1} ℤ) (_v : V),
    affineThomSphere A q ⟶ affineK (D := D₀) (G := G) (P := P) (A := A) (R := R) N Q q V
  diagonal_cycle : ∀ (q : ℕ) (V : ModuleCat.{1} ℤ) (v : V),
    cofiberQuotient (representedMap (A.complementInclusion q)) ≫ map q V v =
      affineCycleSection N Q M q V (A.affine q) (graphCycle G (𝟙 (A.affine q))) v

/-- Actual comparison morphisms between the independently fixed affine
finite-cycle quotient and native reduced-torus Tate realization. -/
structure AffineTateMapSystem where
  map : ∀ (q : ℕ) (V : ModuleCat.{1} ℤ),
    affineK (D := D₀) (G := G) (P := P) (A := A) (R := R) N Q q V ⟶
      K B I Q (2 * (q : ℤ)) (q : ℤ) V

variable (V : AffineTateMapSystem (N := N) (B := B) (I := I) (Q := Q))

/-- Theorem2.1's weak-equivalence assertion is an output predicate on the
actual comparison morphisms, never a cohomology definition. -/
def IsMotivicComparison : Prop :=
  ∀ (q : ℕ) (A₁ : ModuleCat.{1} ℤ), MotivicWeakEquivalence A (V.map q A₁)

/-- Canonical coefficient change of those same actual comparison morphisms. -/
def IsCoefficientNatural : Prop :=
  ∀ (q : ℕ) (A₁ A₂ : ModuleCat.{1} ℤ) (a : A₁ ⟶ A₂),
    (motivicQ A).map ((affineKFunctor (D := D₀) (G := G) (P := P)
      (A := A) (R := R) N Q q).map a ≫ V.map q A₂) =
    (motivicQ A).map (V.map q A₁ ≫
      MotivicEilenbergMacLaneModels.coefficientMap B I Q (2 * (q : ℤ)) (q : ℤ) a)

/-- Literal reindexing along equal integer degrees/weights. -/
def reindexK {p q p' q' : ℤ} (hp : p = p') (hq : q = q') (A₁ : ModuleCat.{1} ℤ) :
    K B I Q p q A₁ ⟶ K B I Q p' q' A₁ := by
  subst p'
  subst q'
  exact 𝟙 _

variable {J₀ : TorusConcatenation A}
  {M₀ : SingularCycleProduct (S := S) N T J₀} {Z : EilenbergZilberModel N}
  {V₀ : NegativeTensorComparison N}
  {L : CoefficientMultiplicationSystem N T B M₀ Z V₀}
  {F₀ : KFlatResolutionSystem N} {D : DerivedTensorSource N F₀}
  {H : DerivedTensorShifts N F₀ D} {M₁ : ReducedSmashComultiplication N F}
  {hF : IsFreeTensorComparison N F₀ D F}
  (K₀ : PointedTateProducts N B I Q F J L F₀ D H M₁ hF)
  (E₀ : AffineCycleProduct (D := D₀) (G := G) (P := P) (A := A) (R := R) N Q E M)

/-- The exact multiplication comparison in H_•, on actual native cycle
and pointed Tate maps; no point-set strict multiplicativity is assumed. -/
def IsMultiplicative : Prop :=
  ∀ (q r : ℕ) (R₁ : Type 1) [CommRing R₁],
    let C₁ : ModuleCat.{1} ℤ := ModuleCat.of ℤ R₁
    let μ := ringCoefficientMultiplication R₁
    (motivicQ A).map (E₀.map q r C₁ C₁ C₁ μ ≫ V.map (q + r) C₁) =
    (motivicQ A).map (smashMap (V.map q C₁) (V.map r C₁) ≫
      K₀.map (2 * (q : ℤ)) (q : ℤ) (2 * (r : ℤ)) (r : ℤ) C₁ C₁ C₁ μ ≫
      reindexK (N := N) (B := B) (I := I) (Q := Q)
        (show 2 * (q : ℤ) + 2 * (r : ℤ) = 2 * ((q + r : ℕ) : ℤ) from by omega)
        (show (q : ℤ) + (r : ℤ) = ((q + r : ℕ) : ℤ) from by omega) C₁)

/-- Actual finite-cycle realization into the independently defined
native Tate hypercohomology, through the chosen source comparison map. -/
def finiteCycleClass (q : ℕ) (A₁ : ModuleCat.{1} ℤ) (U : SmoothScheme k)
    (z : Cycles U (A.affine q)) (a : A₁) :
    ReducedCohomology B F (representedPointed U) (2 * (q : ℤ)) (q : ℤ) A₁ :=
  realizationToCohomology B I Q F J (representedPointed U)
    (2 * (q : ℤ)) (q : ℤ) A₁ (affineCycleSection N Q M q A₁ U z a ≫ V.map q A₁)

/-- Rank-one source normalization fixes the graph/Thom orientation by the
native torus/cofiber boundary, not by an arbitrary class called a generator. -/
def HasRankOneNormalization
    (T₀ : AffineThomCycleSections (D₀ := D₀) (G := G) (P := P)
      (A := A) (R := R) (N := N) (Q := Q) (M := M))
    (O : TorusOpenAffine (P := P) (A := A)) (R₀ : RelativeA1CofiberSource O)
    (C₀ : MotivicCofiberComparisons.CofiberChainSource F (relativeTorusMap O))
    (L₀ : TorusCycleLinearization (S := S) T F)
    (U₀ : IntegerCoefficientInclusions (T := T) (N := N) (B := B)) : Prop :=
  realizationToCohomology B I Q F J (affineThomSphere A 1) 2 1 integerCoefficients
    (T₀.map 1 integerCoefficients 1 ≫ V.map 1 integerCoefficients) =
  rankOneThomClass (T := T) (F := F) (N := N) (B := B) O R₀ C₀ L₀ U₀

end MathlibExt.AlgebraicGeometry.MotivicAffineTateComparisons

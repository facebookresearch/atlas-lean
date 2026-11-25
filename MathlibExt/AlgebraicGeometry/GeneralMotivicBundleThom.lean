/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeneralMotivicBundleFrameMaps
public import MathlibExt.AlgebraicGeometry.MotivicAffineTateComparisons

/-!
# General bundle Thom classes and the actual Thom action

The affine orientation is the original diagonal finite-cycle class under
the fixed affine-to-Tate comparison. A bundle class is normalized on actual
framed open neighbourhoods of every generic component. This expresses the
generic restriction normalization of Voevodsky Corollary 4.4 through its
finite-type spread; it is stronger than an unnormalized choice of a class.

The action uses the native external cup and the bundle diagonal, fixed on
every original simplex by (f,e) ↦ ((f,p(e)),e). Its bijectivity is a theorem
output. No Thom isomorphism is used to define the class or the action.

Source: Voevodsky, arXiv:math/0107109v1, Lemma 4.2, Proposition 4.3,
Corollary 4.4 and Construction 5.1. The coefficient complexes and their
comparison maps retain the separate source normalization and proof requests.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeneralMotivicBundleThom

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels NisnevichTransferModels
open MotivicStandardSchemes MotivicBundleModels GeneralMotivicBundleFrameMaps
open PointedMotivicModels PointedMotivicQuotients
open ReducedMotivicCohomologyModels MotivicRealizationComparisons
open MotivicCohomologyProducts MotivicTensorOperations MotivicCycleProducts
open MotivicAffineTateComparisons EffectiveMotivicComplexModels
open MotivicEilenbergMacLaneModels MotivicTorusClassModels
open MotivicAffineQuotientModels
open MotivicPointedProducts MotivicTateThomModels MotivicCofiberComparisons

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]

/-- The original scheme map viewed as a constant represented simplex. -/
def representedSection (X : SmoothScheme k) (n : SimplexCategoryᵒᵖ)
    (U : (SmoothScheme k)ᵒᵖ) (e : U.unop ⟶ X) :
    ((representedPointed X).right.obj U).obj n := some (ULift.up e)

/-- The original total-space section in the literal pointed Thom quotient. -/
def totalThomSection {X : SmoothScheme k} {M : X.scheme.left.Modules} {d : ℕ}
    (G : BundleGeometry X M d) (n : SimplexCategoryᵒᵖ)
    (U : (SmoothScheme k)ᵒᵖ) (e : U.unop ⟶ G.smoothTotal) :
    (G.thom.right.obj U).obj n :=
  (((cofiberQuotient (representedMap G.complementInclusion)).right.app U).app n)
    (representedSection G.smoothTotal n U e)

/-- Native product and smash quotient on the original presheaf simplices. -/
def smashSection (X Y : PointedSpaces (k := k)) (n : SimplexCategoryᵒᵖ)
    (U : (SmoothScheme k)ᵒᵖ) (x : (X.right.obj U).obj n) (y : (Y.right.obj U).obj n) :
    ((smash X Y).right.obj U).obj n :=
  (((smashQuotient X Y).app U).app n) (productSimplex X Y n U x y)

/-- Every bundle diagonal map is fixed on all original product generators. -/
structure BundleThomDiagonals {X : SmoothScheme k} {M : X.scheme.left.Modules} {d : ℕ}
    (G : BundleGeometry X M d) where
  baseMap : G.thom ⟶ smash (representedPointed X) G.thom
  baseNormalization : ∀ (n : SimplexCategoryᵒᵖ)
    (U : (SmoothScheme k)ᵒᵖ) (e : U.unop ⟶ G.smoothTotal),
    (((baseMap).right.app U).app n) (totalThomSection G n U e) =
      smashSection (representedPointed X) G.thom n U
        (representedSection X n U (e ≫ G.projection)) (totalThomSection G n U e)
  map : ∀ F : PointedSpaces (k := k),
    smash F G.thom ⟶ smash (smash F (representedPointed X)) G.thom
  normalization : ∀ (F : PointedSpaces (k := k)) (n : SimplexCategoryᵒᵖ)
    (U : (SmoothScheme k)ᵒᵖ) (s : (F.right.obj U).obj n) (e : U.unop ⟶ G.smoothTotal),
    (((map F).right.app U).app n)
      (smashSection F G.thom n U s (totalThomSection G n U e)) =
    smashSection (smash F (representedPointed X)) G.thom n U
      (smashSection F (representedPointed X) n U s
        (representedSection X n U (e ≫ G.projection))) (totalThomSection G n U e)

variable {D₀ : CompositionSystem k} {G₀ : GraphSystem k}
  [CorrespondenceLaws D₀ G₀] [CorrespondenceAdditivity D₀ G₀]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D₀ G₀ P E} {A : StandardSchemes P}
  {R : RepresentableSystem D₀ G₀} {S : TransferSheafificationModel D₀ G₀}
  {T : CycleComplexSystem (D := D₀) (G := G₀) (P := P) (E := E)
    (C := C) (A := A) (R := R)}
  (N : NisTensorSystem k) [N.functor.Additive] [∀ H, (N.functor.obj H).Additive]
  (B : CoefficientComplexSystem (D := D₀) (G := G₀) (P := P) (E := E)
    (C := C) (A := A) (R := R) (S := S) T N)
  (I : KInjectiveResolutionSystem k) (Q : PointedSimplicialModuleFunctor k)
  (F : ReducedFreeNisSystem k) (J : ReducedFreeAdjunction F Q)
  {Msec : ModuleSectionSystem Q}
  (V : AffineTateMapSystem (N := N) (B := B) (I := I) (Q := Q))
  (T₀ : AffineThomCycleSections (D₀ := D₀) (G := G₀) (P := P)
    (A := A) (R := R) (N := N) (Q := Q) (M := Msec))

/-- The affine class is the actual diagonal cycle under the original Tate comparison. -/
def affineOrientation (d : ℕ) :
    ReducedCohomology B F (affineThomSphere A d) (2 * (d : ℤ)) (d : ℤ) integerCoefficients :=
  realizationToCohomology B I Q F J (affineThomSphere A d)
    (2 * (d : ℤ)) (d : ℤ) integerCoefficients
      (T₀.map d integerCoefficients 1 ≫ V.map d integerCoefficients)

/-- Generic-point normalization is witnessed on actual finite-type framed open neighbourhoods. -/
def HasGenericNormalization {X : SmoothScheme k} {M : X.scheme.left.Modules} {d : ℕ}
    (G : BundleGeometry X M d)
    (t : ReducedCohomology B F G.thom (2 * (d : ℤ)) (d : ℤ) integerCoefficients) : Prop :=
  ∀ z : irreducibleComponents X.scheme.left,
    ∃ (U : SmoothScheme k) (j : U ⟶ X),
      IsOpenImmersion j.left ∧ z.2.1.genericPoint ∈ Set.range j.left ∧
      ∃ (H : BundleGeometry U ((Scheme.Modules.pullback j.left).obj M) d)
        (Cj : ComplementMap H G j (𝟙 _))
        (φ : ((Scheme.Modules.pullback j.left).obj M) ≅
          SheafOfModules.free (R := U.scheme.left.ringCatSheaf) (Fin d))
        (Cφ : FrameComplementMap A H φ),
      ReducedMotivicCohomologyModels.pullback B F (thomMap H G j (𝟙 _) Cj)
        (2 * (d : ℤ)) (d : ℤ) integerCoefficients t =
      ReducedMotivicCohomologyModels.pullback B F (frameThomMap A H φ Cφ)
        (2 * (d : ℤ)) (d : ℤ) integerCoefficients (affineOrientation N B I Q F J V T₀ d)

/-- The class belongs to the actual bundle Thom group and retains its source normalization. -/
structure ThomClass {X : SmoothScheme k} {M : X.scheme.left.Modules} {d : ℕ}
    (G : BundleGeometry X M d) where
  value : ReducedCohomology B F G.thom (2 * (d : ℤ)) (d : ℤ) integerCoefficients
  genericNormalization : HasGenericNormalization N B I Q F J V T₀ G value

/-- The Euler class is the original zero-section pullback of the normalized bundle class. -/
def euler {X : SmoothScheme k} {M : X.scheme.left.Modules} {d : ℕ}
    (G : BundleGeometry X M d) (t : ThomClass N B I Q F J V T₀ G) :
    ReducedCohomology B F (representedPointed X)
      (2 * (d : ℤ)) (d : ℤ) integerCoefficients :=
  eulerClass B F G integerCoefficients t.value

variable {J₀ : TorusConcatenation A}
  {M₀ : SingularCycleProduct (S := S) N T J₀} {Z : EilenbergZilberModel N}
  {V₀ : NegativeTensorComparison N}
  (L : CoefficientMultiplicationSystem N T B M₀ Z V₀)
  (F₀ : KFlatResolutionSystem N) (D : DerivedTensorSource N F₀)
  (H : DerivedTensorShifts N F₀ D) (M₁ : ReducedSmashComultiplication N F)
  (hF : IsFreeTensorComparison N F₀ D F)

/-- The scalar transport to the original lifted integer coefficient is fixed on every pure tensor. -/
structure IntegerCoefficientUnits where
  map : ∀ A₁ : ModuleCat.{1} ℤ, TensorProduct ℤ A₁ integerCoefficients →ₗ[ℤ] A₁
  normalization : ∀ (A₁ : ModuleCat.{1} ℤ) (a : A₁) (z : ℤ),
    map A₁ (TensorProduct.tmul ℤ a (ULift.up z)) = z • a

variable (U₀ : IntegerCoefficientUnits)

/-- These are exactly the independent source properties of the canonical affine-to-Tate output. -/
structure CanonicalAffineSource
    (K₀ : PointedTateProducts N B I Q F J L F₀ D H M₁ hF)
    (E₀ : AffineCycleProduct (D := D₀) (G := G₀) (P := P) (A := A) (R := R)
      N Q E Msec)
    (O : TorusOpenAffine (P := P) (A := A)) (R₀ : RelativeA1CofiberSource O)
    (C₀ : CofiberChainSource F (relativeTorusMap O))
    (L₀ : TorusCycleLinearization (S := S) T F)
    (Z₀ : IntegerCoefficientInclusions (T := T) (N := N) (B := B)) : Prop where
  weak : IsMotivicComparison (N := N) (B := B) (I := I) (Q := Q) V
  coefficient : IsCoefficientNatural (N := N) (B := B) (I := I) (Q := Q) V
  multiplicative : IsMultiplicative (N := N) (B := B) (I := I) (Q := Q) (F := F)
    (J := J) (M := Msec) V K₀ E₀
  rankOne : HasRankOneNormalization (N := N) (B := B) (I := I) (Q := Q) (F := F)
    (J := J) (M := Msec) V T₀ O R₀ C₀ L₀ Z₀

/-- The unparameterized Thom action is native cup and the original bundle-base diagonal. -/
def baseThomAction {X : SmoothScheme k} {M : X.scheme.left.Modules} {d : ℕ}
    (G : BundleGeometry X M d) (Δ : BundleThomDiagonals G)
    (t : ThomClass N B I Q F J V T₀ G) (p q : ℤ) (A₁ : ModuleCat.{1} ℤ)
    (u : ReducedCohomology B F (representedPointed X) p q A₁) :
    ReducedCohomology B F G.thom (p + 2 * (d : ℤ)) (q + (d : ℤ)) A₁ :=
  ReducedMotivicCohomologyModels.pullback B F Δ.baseMap
    (p + 2 * (d : ℤ)) (q + (d : ℤ)) A₁
      (externalCup N B L F₀ D H F M₁ hF (representedPointed X) G.thom
        p q (2 * (d : ℤ)) (d : ℤ) A₁ integerCoefficients A₁
        (U₀.map A₁) u t.value)

/-- The actual general Thom action is external cup followed by the original bundle diagonal. -/
def thomAction {X : SmoothScheme k} {M : X.scheme.left.Modules} {d : ℕ}
    (G : BundleGeometry X M d) (Δ : BundleThomDiagonals G)
    (t : ThomClass N B I Q F J V T₀ G) (W : PointedSpaces (k := k))
    (p q : ℤ) (A₁ : ModuleCat.{1} ℤ)
    (u : ReducedCohomology B F (smash W (representedPointed X)) p q A₁) :
    ReducedCohomology B F (smash W G.thom) (p + 2 * (d : ℤ)) (q + (d : ℤ)) A₁ :=
  ReducedMotivicCohomologyModels.pullback B F (Δ.map W)
    (p + 2 * (d : ℤ)) (q + (d : ℤ)) A₁
      (externalCup N B L F₀ D H F M₁ hF
        (smash W (representedPointed X)) G.thom p q (2 * (d : ℤ)) (d : ℤ)
        A₁ integerCoefficients A₁ (U₀.map A₁) u t.value)

end MathlibExt.AlgebraicGeometry.GeneralMotivicBundleThom

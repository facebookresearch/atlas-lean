/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicPowerCoefficients
public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.SimplicialSet.Pointed.Circle

/-!
# Native circle/Tate suspensions and extension to every integer bidegree

The simplicial circle is the constant presheaf on the actual quotient
Delta[1]/boundary Delta[1], with its original quotient basepoint. The
integral orientation is normalized on the ordered identity edge by the
actual degree-zero torus cycle. The torus orientation is the existing
native graph class sigma_t.

Suspension isomorphisms have their action fixed by native external cup
with these integral classes and the original coefficient-unit map.
Their existence is a source request independent of any power identity.

The extension in Proposition 2.6 is computed by sufficient nonnegative
circle and torus suspensions to degree (2d,d), applying the diagonal
coefficient operation, and using the same suspension inverse on output.
The construction covers all integer p,q and exact integer Tate shifts.

Source: Voevodsky, arXiv:math/0107109v1, Theorem 2.4,
Proposition 2.6, Equation 9.2 and the extension following it.
The original circle port retains Tau Ceti's Apache attribution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicPowerSuspensions

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels NisnevichTransferModels
open MotivicStandardSchemes EffectiveMotivicComplexModels PointedMotivicModels
open PointedMotivicQuotients ReducedMotivicCohomologyModels MotivicRealizationComparisons
open MotivicAffineQuotientModels MotivicAffineTateComparisons
open MotivicCycleProducts MotivicTensorOperations MotivicCohomologyProducts
open GeneralMotivicBundleThom MotivicBocksteinModels MotivicTorusClassModels
open MotivicPowerCoefficients
open scoped Simplicial ZeroObject

variable {k : Type} [Field k]

/-- The underlying native circle, lifted only to the universe of motivic spaces. -/
def circlePresheaf : Spaces (k := k) :=
  (Functor.const (SmoothScheme k)ᵒᵖ).obj ((SSet.uliftFunctor.{1}).obj SSet.S1)

/-- Its point is the actual collapsed boundary vertex. -/
def circleBasepoint : 𝟙_ (Spaces (k := k)) ⟶ circlePresheaf (k := k) where
  app U := SSet.const (ULift.up
    (SSet.yonedaEquiv MathlibExt.SpectraSource.SSet.S1.basepoint))
  naturality U V f := by ext n x; rfl

/-- The simplicial suspension source is the actual pointed native quotient. -/
def simplicialCircle : PointedSpaces (k := k) := Under.mk (circleBasepoint (k := k))

/-- The fundamental ordered edge is the image of the identity simplex under the actual quotient. -/
def circleEdge (U : (SmoothScheme k)ᵒᵖ) :
    ((simplicialCircle (k := k)).right.obj U).obj (op ⦋1⦌) :=
  ULift.up (SSet.yonedaEquiv MathlibExt.SpectraSource.SSet.S1.quotient)

variable
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  {D₀ : CompositionSystem k} {G₀ : GraphSystem k}
  [CorrespondenceLaws D₀ G₀] [CorrespondenceAdditivity D₀ G₀]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D₀ G₀ P E} {A : StandardSchemes P}
  {R₀ : RepresentableSystem D₀ G₀} {S₀ : TransferSheafificationModel D₀ G₀}
  (T : CycleComplexSystem (D := D₀) (G := G₀) (P := P) (E := E)
    (C := C) (A := A) (R := R₀))
  (F : ReducedFreeNisSystem k)

/-- The native reduced normalized circle edge, in the extended source degree -1. -/
def reducedCircleEdge (U : (SmoothScheme k)ᵒᵖ)
    (t : ((𝟙_ (Spaces (k := k))).obj U).obj (op ⦋1⦌)) :
    (((reducedComplexFunctor F).obj (simplicialCircle (k := k))).X (-1)).obj.obj U := by
  let C := (reducedSimplicialFunctor F).obj (simplicialCircle (k := k))
  let NC := (AlgebraicTopology.normalizedMooreComplex (NisModules (k := k))).obj C
  exact (((NC.extendXIso negativeEmbedding
      (show (0 : ℤ) - ((1 : ℕ) : ℤ) = -1 by simp)).inv.hom.app U)
    ((((mooreProjection C).f 1).hom.app U)
      (reducedGenerator F (simplicialCircle (k := k)) (op ⦋1⦌) U t (circleEdge U))))

/-- The raw weight-zero target is the original normalized singular degree-zero torus source. -/
def rawWeightZero := (torusChains (S := S₀) T 0).extend negativeEmbedding

/-- The target edge value is compared through the native shift and extension isomorphisms. -/
def rawCircleTarget :
    ((rawWeightZero (S₀ := S₀) T)⟦(1 : ℤ)⟧).X (-1) ⟶ (torusChains (S := S₀) T 0).X 0 :=
  (CochainComplex.shiftFunctorObjXIso (rawWeightZero (S₀ := S₀) T) (1 : ℤ) (-1) 0 (by omega)).hom ≫
    ((torusChains (S := S₀) T 0).extendXIso negativeEmbedding
      (show (0 : ℤ) - ((0 : ℕ) : ℤ) = 0 by simp)).hom

/-- A source cochain has its sign fixed by the original ordered circle edge and point cycle. -/
structure CircleCycleOrientation where
  map : (reducedComplexFunctor F).obj (simplicialCircle (k := k)) ⟶
    (rawWeightZero (S₀ := S₀) T)⟦(1 : ℤ)⟧
  edge : ∀ (U : (SmoothScheme k)ᵒᵖ)
    (t : ((𝟙_ (Spaces (k := k))).obj U).obj (op ⦋1⦌)),
    (((map.f (-1) ≫ rawCircleTarget (S₀ := S₀) T).hom.app U) (reducedCircleEdge F U t)) =
      singularClass T 0 (op ⦋0⦌) U.unop
        (graphCycle G₀ (MotivicFinitePowerCycles.unitMap P
          (P.obj (A.simplex.obj ⦋0⦌) U.unop) ≫ A.torusUnit.inv))

/-- This is the actual raw circle cochain transported to the original Tate complex. -/
def circleTateCochain (L : CircleCycleOrientation (S₀ := S₀) T F) :
    (reducedComplexFunctor F).obj (simplicialCircle (k := k)) ⟶
      (tateComplex (D := D₀) (G := G₀) (P := P) (E := E) (C := C)
        (A := A) (R := R₀) (S := S₀) T 0)⟦(1 : ℤ)⟧ := by
  have ht : tateComplex (D := D₀) (G := G₀) (P := P) (E := E) (C := C)
      (A := A) (R := R₀) (S := S₀) T 0 = (rawWeightZero (S₀ := S₀) T)⟦(0 : ℤ)⟧ := by
    simp only [tateComplex, ite_eq_left (show 0 ≤ (0 : ℤ) from by omega)]
    rfl
  exact L.map ≫ ((shiftFunctorZero (CochainComplex (NisModules (k := k)) ℤ) ℤ).inv.app
    (rawWeightZero (S₀ := S₀) T))⟦(1 : ℤ)⟧' ≫ (eqToHom ht.symm)⟦(1 : ℤ)⟧'

variable (N : NisTensorSystem k) [N.functor.Additive] [∀ H, (N.functor.obj H).Additive]
  (B : CoefficientComplexSystem (D := D₀) (G := G₀) (P := P) (E := E)
    (C := C) (A := A) (R := R₀) (S := S₀) T N)
  (Z : IntegerCoefficientInclusions (N := N) (T := T) (B := B))

attribute [local instance] HasDerivedCategory.standard

/-- Sigma_s is the original oriented edge cochain followed by the native coefficient unit. -/
def circleClass (L : CircleCycleOrientation (S₀ := S₀) T F) :
    ReducedCohomology B F (simplicialCircle (k := k)) 1 0 integerCoefficients :=
  DerivedCategory.Q.map (circleTateCochain T F L ≫ (Z.map 0)⟦(1 : ℤ)⟧') ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app ((B.weightFunctor 0).obj integerCoefficients)

variable {J₀ : TorusConcatenation A}
  {M₀ : SingularCycleProduct (S := S₀) N T J₀} {EZ : EilenbergZilberModel N}
  {V₀ : NegativeTensorComparison N}
  (K₀ : CoefficientMultiplicationSystem N T B M₀ EZ V₀)
  (F₀ : KFlatResolutionSystem N) (D : DerivedTensorSource N F₀)
  (S : DerivedTensorShifts N F₀ D) (M₁ : ReducedSmashComultiplication N F)
  (hF : IsFreeTensorComparison N F₀ D F) (U₀ : IntegerCoefficientUnits)
  (Ls : CircleCycleOrientation (S₀ := S₀) T F) (Lt : TorusCycleLinearization (S := S₀) T F)
  (ell : ℕ)

/-- The source suspension isomorphisms act by the fixed native circle and torus classes. -/
structure SuspensionEquivalences where
  simplicial : ∀ (X : PointedSpaces (k := k)) (p q : ℤ),
    ReducedCohomology B F X p q (ModCoefficients ell) ≃+
      ReducedCohomology B F (smash X (simplicialCircle (k := k))) (p + 1) q (ModCoefficients ell)
  simplicialClass : ∀ (X : PointedSpaces (k := k)) (p q : ℤ)
    (u : ReducedCohomology B F X p q (ModCoefficients ell)),
    simplicial X p q u =
      regrade N (B := B) (R₁ := F) (smash X (simplicialCircle (k := k))) (ModCoefficients ell)
        rfl (by omega)
        (externalCup N B K₀ F₀ D S F M₁ hF X (simplicialCircle (k := k))
          p q 1 0 (ModCoefficients ell) integerCoefficients (ModCoefficients ell)
          (U₀.map (ModCoefficients ell)) u (circleClass T F N B Z Ls))
  torus : ∀ (X : PointedSpaces (k := k)) (p q : ℤ),
    ReducedCohomology B F X p q (ModCoefficients ell) ≃+
      ReducedCohomology B F (smash X (pointedTorus (P := P) (A := A)))
        (p + 1) (q + 1) (ModCoefficients ell)
  torusClass : ∀ (X : PointedSpaces (k := k)) (p q : ℤ)
    (u : ReducedCohomology B F X p q (ModCoefficients ell)),
    torus X p q u =
      externalCup N B K₀ F₀ D S F M₁ hF X (pointedTorus (P := P) (A := A))
        p q 1 1 (ModCoefficients ell) integerCoefficients (ModCoefficients ell)
        (U₀.map (ModCoefficients ell)) u (MotivicTorusClassModels.torusClass T F N B Lt Z)

variable {T F N B Z K₀ F₀ D S M₁ hF U₀ Ls Lt ell}

/-- Degree transport is the literal additive equivalence along equal integer bidegrees. -/
def degreeEquiv (X : PointedSpaces (k := k)) {p q p' q' : ℤ} (hp : p = p') (hq : q = q') :
    ReducedCohomology B F X p q (ModCoefficients ell) ≃+
      ReducedCohomology B F X p' q' (ModCoefficients ell) := by
  subst p'
  subst q'
  exact AddEquiv.refl _

/-- Actual iterated simplicial-circle smash, with the original source convention. -/
def simplicialWord (X : PointedSpaces (k := k)) (a : ℕ) : PointedSpaces (k := k) :=
  Nat.rec X (fun _ Y => smash Y (simplicialCircle (k := k))) a

/-- Actual iterated torus-circle smash. -/
def torusWord (X : PointedSpaces (k := k)) (b : ℕ) : PointedSpaces (k := k) :=
  Nat.rec X (fun _ Y => smash Y (pointedTorus (P := P) (A := A))) b

/-- The native source object of the two kinds of suspension. -/
def suspensionWord (X : PointedSpaces (k := k)) (a b : ℕ) : PointedSpaces (k := k) :=
  torusWord (A := A) (simplicialWord X a) b

variable (σ : SuspensionEquivalences T F N B Z K₀ F₀ D S M₁ hF U₀ Ls Lt ell)

/-- Iteration of the actual sigma_s suspension equivalence. -/
def simplicialSuspensionEquiv (X : PointedSpaces (k := k)) (p q : ℤ) (a : ℕ) :
    ReducedCohomology B F X p q (ModCoefficients ell) ≃+
      ReducedCohomology B F (simplicialWord X a) (p + (a : ℤ)) q (ModCoefficients ell) := by
  induction a with
  | zero => exact degreeEquiv X (by simp) rfl
  | succ a ih =>
      exact ih.trans ((σ.simplicial (simplicialWord X a) (p + (a : ℤ)) q).trans
        (degreeEquiv _ (by push_cast; ring) rfl))

/-- Iteration of the actual sigma_t suspension equivalence. -/
def torusSuspensionEquiv (X : PointedSpaces (k := k)) (p q : ℤ) (b : ℕ) :
    ReducedCohomology B F X p q (ModCoefficients ell) ≃+
      ReducedCohomology B F (torusWord (A := A) X b) (p + (b : ℤ)) (q + (b : ℤ))
        (ModCoefficients ell) := by
  induction b with
  | zero => exact degreeEquiv X (by simp) (by simp)
  | succ b ih =>
      exact ih.trans ((σ.torus (torusWord (A := A) X b) (p + (b : ℤ)) (q + (b : ℤ))).trans
        (degreeEquiv _ (by push_cast; ring) (by push_cast; ring)))

/-- Full suspension equivalence, retaining both native circle orientations. -/
def wordSuspensionEquiv (X : PointedSpaces (k := k)) (p q : ℤ) (a b : ℕ) :
    ReducedCohomology B F X p q (ModCoefficients ell) ≃+
      ReducedCohomology B F (suspensionWord (A := A) X a b)
        (p + (a : ℤ) + (b : ℤ)) (q + (b : ℤ)) (ModCoefficients ell) :=
  (simplicialSuspensionEquiv σ X p q a).trans
    (torusSuspensionEquiv σ (simplicialWord X a) (p + (a : ℤ)) q b)

/-- Enough actual torus suspensions to make both the Tate weight and the simplicial count nonnegative. -/
def extensionTorusCount (p q : ℤ) : ℕ := (max 0 (max (-q) (p - 2 * q))).toNat

/-- The complementary number of actual simplicial suspensions. -/
def extensionSimplicialCount (p q : ℤ) : ℕ :=
  (2 * q - p + (extensionTorusCount p q : ℤ)).toNat

/-- The diagonal degree reached by these actual suspension counts. -/
def extensionDiagonalDegree (p q : ℤ) : ℕ := (q + (extensionTorusCount p q : ℤ)).toNat

/-- The construction reaches exactly a nonnegative diagonal degree for every integer p,q. -/
theorem extensionCounts_diagonal (p q : ℤ) :
    p + (extensionSimplicialCount p q : ℤ) + (extensionTorusCount p q : ℤ) =
      2 * (extensionDiagonalDegree p q : ℤ) ∧
    q + (extensionTorusCount p q : ℤ) = (extensionDiagonalDegree p q : ℤ) := by
  dsimp [extensionSimplicialCount, extensionTorusCount, extensionDiagonalDegree]
  omega

/-- Proposition 2.6's actual extension: suspend, apply the diagonal operation, and desuspend with the same source. -/
def extendDiagonalOperation (dp dq : ℤ)
    (diagonal : ∀ (d : ℕ) (X : PointedSpaces (k := k)),
      ReducedCohomology B F X (2 * (d : ℤ)) (d : ℤ) (ModCoefficients ell) →
        ReducedCohomology B F X (2 * (d : ℤ) + dp) ((d : ℤ) + dq) (ModCoefficients ell))
    (X : PointedSpaces (k := k)) (p q : ℤ)
    (u : ReducedCohomology B F X p q (ModCoefficients ell)) :
    ReducedCohomology B F X (p + dp) (q + dq) (ModCoefficients ell) := by
  let a := extensionSimplicialCount p q
  let b := extensionTorusCount p q
  let d := extensionDiagonalDegree p q
  have hp : p + (a : ℤ) + (b : ℤ) = 2 * (d : ℤ) := (extensionCounts_diagonal p q).1
  have hq : q + (b : ℤ) = (d : ℤ) := (extensionCounts_diagonal p q).2
  let input := (wordSuspensionEquiv σ X p q a b).trans (degreeEquiv _ hp hq)
  let output := (wordSuspensionEquiv σ X (p + dp) (q + dq) a b).trans
    (degreeEquiv _ (show p + dp + (a : ℤ) + (b : ℤ) = 2 * (d : ℤ) + dp from by omega)
      (show q + dq + (b : ℤ) = (d : ℤ) + dq from by omega))
  exact output.symm (diagonal d (suspensionWord (A := A) X a b) (input u))

end MathlibExt.AlgebraicGeometry.MotivicPowerSuspensions

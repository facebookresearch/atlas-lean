/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicCohomologyProducts

/-!
# The canonical torus class on G_m pointed at one

The point is the actual unit-coordinate insertion. Its reduced-free
class is fixed by every actual graph U×Delta^n -> G_m and the reduced
torus cokernel. Normalized Moore inclusion, negative extension and native
shift cancellation place that class in the published Z(1)[1]. Integer
coefficient inclusion is fixed on each pure tensor with the constant unit.
These definitions fix the orientation used by the affine/Tate comparison.

Sources: Mazza--Voevodsky--Weibel, Definition 3.1 and Lectures 3/14;
Voevodsky arXiv:math/0107109v1, Section 2, the class sigma_t.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicTorusClassModels

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open FiniteTransferCycleModels FiniteTransferProductModels
open NisnevichTransferModels MotivicStandardSchemes
open EffectiveMotivicComplexModels PointedMotivicModels
open ReducedMotivicCohomologyModels MotivicRealizationComparisons
open MotivicCycleProducts MotivicTensorOperations MotivicCohomologyProducts
open PointedMotivicQuotients
open scoped Simplicial ZeroObject

/-- Actual integral coefficients in the fixed coefficient universe. -/
abbrev integerCoefficients : ModuleCat.{1} ℤ := ModuleCat.of ℤ (ULift.{1} ℤ)

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  {D : CompositionSystem k} {G : GraphSystem k}
  [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D G P E} {A : StandardSchemes P}
  {R : RepresentableSystem D G} {S : TransferSheafificationModel D G}

/-- The actual torus unit, through the coordinate insertion at one. -/
def torusPoint : P.unit ⟶ A.torus 1 := A.torusUnit.inv ≫ A.unitInsertion 0 0

/-- G_m pointed at one, as the literal pointed unit quotient. -/
def pointedTorus : PointedSpaces (k := k) :=
  cofiber (representedMap (torusPoint (P := P) (A := A)))

/-- The actual graph simplex in that pointed torus quotient. -/
def torusSimplex (n : SimplexCategoryᵒᵖ) (U : SmoothScheme k) (g : U ⟶ A.torus 1) :
    ((pointedTorus (P := P) (A := A)).right.obj (op U)).obj n :=
  (((cofiberQuotient (representedMap (torusPoint (P := P) (A := A)))).right.app (op U)).app n)
    (some (ULift.up g))

variable
  (T : CycleComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R)) (F : ReducedFreeNisSystem k)

/-- The source linearization is fixed on every graph and every algebraic
simplex, with the point-one generator killed by the actual torus cokernel. -/
structure TorusCycleLinearization where
  map : (reducedSimplicialFunctor F).obj (pointedTorus (P := P) (A := A)) ⟶
    singularNis (D := D) (G := G) (P := P) (E := E) (C := C)
      (A := A) (R := R) (S := S) T 1
  graph : ∀ (n : SimplexCategoryᵒᵖ) (U : SmoothScheme k)
    (g : U ⟶ A.torus 1) (t : ((𝟙_ (Spaces (k := k))).obj (op U)).obj n),
    (((map.app n).hom.app (op U))
      (reducedGenerator F (pointedTorus (P := P) (A := A)) n (op U) t
        (torusSimplex (P := P) (A := A) n U g))) =
      singularClass T 1 n U
        (graphCycle G ((P.geometry (A.simplex.obj n.unop) U).snd ≫ g))

/-- The native torus cochain class, including the actual Moore-to-
alternating inclusion and the standard cancellation of the two shifts. -/
def torusClassCochain (L : TorusCycleLinearization (S := S) T F) :
    (reducedComplexFunctor F).obj (pointedTorus (P := P) (A := A)) ⟶
      (tateComplex (D := D) (G := G) (P := P) (E := E) (C := C)
        (A := A) (R := R) (S := S) T (1 : ℤ))⟦(1 : ℤ)⟧ := by
  let U := (torusChains (S := S) T 1).extend negativeEmbedding
  have ht : tateComplex (D := D) (G := G) (P := P) (E := E) (C := C)
      (A := A) (R := R) (S := S) T (1 : ℤ) = U⟦(-1 : ℤ)⟧ := by
    simp only [tateComplex, ite_eq_left (show 0 ≤ (1 : ℤ) from by omega)]
    rfl
  exact (negativeEmbedding.extendFunctor (NisModules (k := k))).map
    ((AlgebraicTopology.normalizedMooreComplex _).map L.map ≫
      mooreInclusion (singularNis (D := D) (G := G) (P := P) (E := E) (C := C)
        (A := A) (R := R) (S := S) T 1)) ≫
    (shiftFunctorZero (CochainComplex (NisModules (k := k)) ℤ) ℤ).inv.app U ≫
    (shiftFunctorAdd' _ (-1 : ℤ) 1 0 (by omega)).hom.app U ≫
    (eqToHom ht.symm)⟦(1 : ℤ)⟧'

variable (N : NisTensorSystem k) [N.functor.Additive] [∀ H, (N.functor.obj H).Additive]
  (B : CoefficientComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R) (S := S) T N)

/-- The coefficient-unit map is fixed on every actual local tensor, and
contains no cohomology or motivic equivalence field. -/
structure IntegerCoefficientInclusions where
  map : ∀ q : ℤ,
    tateComplex (D := D) (G := G) (P := P) (E := E) (C := C)
      (A := A) (R := R) (S := S) T q ⟶ (B.weightFunctor q).obj integerCoefficients
  unit : ∀ (q n : ℤ) (U : (SmoothScheme k)ᵒᵖ)
    (x : ((tateComplex (D := D) (G := G) (P := P) (E := E) (C := C)
      (A := A) (R := R) (S := S) T q).X n).obj.obj U),
    (((map q).f n).hom.app U) x =
      coefficientElement N T B integerCoefficients q n U x 1

attribute [local instance] HasDerivedCategory.standard

/-- The canonical sigma_t is native reduced hypercohomology of the
actual torus graph linearization and integer-unit coefficient inclusion. -/
def torusClass (L : TorusCycleLinearization (S := S) T F)
    (U : IntegerCoefficientInclusions (N := N) (T := T) (B := B)) :
    ReducedCohomology B F (pointedTorus (P := P) (A := A)) 1 1 integerCoefficients :=
  DerivedCategory.Q.map (torusClassCochain T F L ≫ (U.map 1)⟦(1 : ℤ)⟧') ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app ((B.weightFunctor 1).obj integerCoefficients)

end MathlibExt.AlgebraicGeometry.MotivicTorusClassModels

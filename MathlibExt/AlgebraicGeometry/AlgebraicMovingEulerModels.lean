/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AlgebraicFixedChowModels
public import MathlibExt.AlgebraicGeometry.DerivedTwoTermObstructionModels

/-!
# Moving-dual Euler operations and their finite geometric inverse

Every Chern cap is computed from the actual dual moving bundle.
The weight is the negative of its original geometric character.
The Laurent coefficients and all native Chern maps are fixed. The
inverse is a finite geometric series in the positive-Chern-degree
perturbation, bounded by the actual dimension of the fixed scheme.
Invertibility is a theorem about that formula, not input data.

Reference: Graber--Pandharipande alg-geom/9708001v2, Section1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.AlgebraicMovingEulerModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open IntegralChowChernModels AlgebraicWeightBundleModels AlgebraicFixedChowModels
open AlgebraicEquivariantCoefficientModels CoherentCurveLinearSeries
open scoped DirectSum TensorProduct

variable (F : SchemeData)

/-- The genuine cap on the integral ordinary Chow coefficients, extended to Q. -/
def ordinaryCap {E : F.scheme.left.Modules} {r : ℕ} (C : ChernConstruction F E r) (n : ℕ) :
    GradedOrdinary F →ₗ[ℚ] GradedOrdinary F :=
  DirectSum.toModule (M := OrdinaryChow F) ℚ ℤ (GradedOrdinary F) (fun (i : ℤ) =>
    (DirectSum.lof ℚ ℤ (OrdinaryChow F) (i-n)).comp (StackChowGroups.rationalMap (chernCap C n i)))

/-- The same actual cap on the Laurent tensor coefficients. -/
def laurentCap {E : F.scheme.left.Modules} {r : ℕ} (C : ChernConstruction F E r) (n : ℕ) :
    FormalChow F →ₗ[ℚ] FormalChow F :=
  TensorProduct.map (LinearMap.id : Coefficients →ₗ[ℚ] Coefficients) (ordinaryCap F C n)

/-- The weight-scaled coefficient acts by literal Laurent scalar multiplication. -/
def scalarOperator (c : Coefficients) : Module.End ℚ (FormalChow F) :=
  { toFun := fun a => c • a
    map_add' := by intro a b; exact smul_add c a b
    map_smul' := by intro r a; exact smul_comm c r a }

/-- The actual weighted Euler cap sum_i (w t)^(r-i)c_i(E). -/
def weightedEuler {E : F.scheme.left.Modules} {r : ℕ} (C : ChernConstruction F E r) (w : ℤ) :
    Module.End ℚ (FormalChow F) :=
  ∑ i ∈ Finset.range (r+1),
    (scalarOperator F ((algebraMap ℚ Coefficients (w : ℚ)) * LaurentPolynomial.T 1)^(r-i)) *
      laurentCap F C i

/-- The actual ordinary dual module, without a separately supplied virtual bundle. -/
def dualModule (E : F.scheme.left.Modules) : F.scheme.left.Modules :=
  BundleTrace.homSheaf F.scheme.left E (structureModule F.scheme.left)

/-- A dual moving summand is fixed by its actual original character, module and rank. -/
structure DualMovingSummand where
  original : F.scheme.left.Modules
  rank : ℕ
  originalBundle : AlgebraicBundleGeometry.IsBundle original rank
  character : Character Gm
  integer : IntegerCharacter character
  moving : integer.weight ≠ 0
  chern : ChernConstruction F (dualModule F original) rank

/-- Dualizing changes the actual geometric integer weight by a minus sign. -/
def dualEuler (E : DualMovingSummand F) : Module.End ℚ (FormalChow F) :=
  weightedEuler F E.chern (-E.integer.weight)

/-- The product uses the actual finite list of moving summands. -/
def movingEuler (E : List (DualMovingSummand F)) : Module.End ℚ (FormalChow F) :=
  (E.map (dualEuler F)).foldl (fun a b => a*b) 1

def movingRank (E : List (DualMovingSummand F)) : ℕ :=
  (E.map DualMovingSummand.rank).sum

/-- The leading coefficient is fixed by the actual nonzero dual weights and ranks. -/
def leadingCoefficient (E : List (DualMovingSummand F)) : Coefficients :=
  algebraMap ℚ Coefficients ((E.map (fun e => (-e.integer.weight : ℚ)^e.rank)).prod : ℚ) *
    LaurentPolynomial.T (movingRank F E)

/-- Its inverse uses the actual rational weight product and inverse Laurent monomial. -/
def leadingInverse (E : List (DualMovingSummand F)) : Coefficients :=
  algebraMap ℚ Coefficients (((E.map (fun e => (-e.integer.weight : ℚ)^e.rank)).prod : ℚ)⁻¹) *
    LaurentPolynomial.T (-(movingRank F E : ℤ))

/-- The perturbation has strictly positive ordinary Chern degree. -/
def eulerPerturbation (E : List (DualMovingSummand F)) : Module.End ℚ (FormalChow F) :=
  scalarOperator F (leadingInverse F E) * movingEuler F E - 1

/-- The inverse is a literal finite series using the actual scheme-dimension bound. -/
def inverseMovingEuler (E : List (DualMovingSummand F)) (dimensionBound : ℕ) :
    Module.End ℚ (FormalChow F) :=
  (∑ k ∈ Finset.range (dimensionBound+1), (-eulerPerturbation F E)^k) *
    scalarOperator F (leadingInverse F E)

/-- Chern models use each original weight summand's actual dual module and rank. -/
structure DecompositionChernData {X : Over base} [ModObj Gm X]
    {E : X.left.Modules} {L : LinearizedLineBundles.Linearization Gm X E}
    {i : F.scheme ⟶ X} {hi : TorusFixedSchemeModels.FixedPoint Gm X i}
    (W : WeightDecomposition L i hi) where
  weights : ∀ j : Fin W.count, IntegerCharacter (W.character j)
  chern : ∀ j : Fin W.count, ChernConstruction F (dualModule F (W.bundle j)) (W.rank j)

/-- The moving list is computed from the original decomposition, never supplied independently. -/
def decompositionSummands {X : Over base} [ModObj Gm X]
    {E : X.left.Modules} {L : LinearizedLineBundles.Linearization Gm X E}
    {i : F.scheme ⟶ X} {hi : TorusFixedSchemeModels.FixedPoint Gm X i}
    {W : WeightDecomposition L i hi} (C : DecompositionChernData F W) :
    List (DualMovingSummand F) := by
  classical
  exact (List.finRange W.count).filterMap (fun j =>
    if h : (C.weights j).weight ≠ 0 then some {
      original := W.bundle j
      rank := W.rank j
      originalBundle := W.locallyFree j
      character := W.character j
      integer := C.weights j
      moving := h
      chern := C.chern j } else none)

/-- The virtual normal is fixed to E0-dual-moving minus Eminus1-dual-moving. -/
structure VirtualNormalData {X : Over base} [ModObj Gm X]
    (P : DerivedTwoTermObstructionModels.EquivariantObstructionTerms X)
    {i : F.scheme ⟶ X} {hi : TorusFixedSchemeModels.FixedPoint Gm X i}
    (W : DerivedTwoTermObstructionModels.FixedTerms P i hi) where
  zero : DecompositionChernData F W.degreeZero
  negative : DecompositionChernData F W.negative

def inverseVirtualEuler {X : Over base} [ModObj Gm X]
    {P : DerivedTwoTermObstructionModels.EquivariantObstructionTerms X}
    {i : F.scheme ⟶ X} {hi : TorusFixedSchemeModels.FixedPoint Gm X i}
    {W : DerivedTwoTermObstructionModels.FixedTerms P i hi}
    (N : VirtualNormalData F P W) (dimensionBound : ℕ) :
    Module.End ℚ (FormalChow F) :=
  movingEuler F (decompositionSummands F N.negative) *
    inverseMovingEuler F (decompositionSummands F N.zero) dimensionBound

end MathlibExt.AlgebraicGeometry.AlgebraicMovingEulerModels

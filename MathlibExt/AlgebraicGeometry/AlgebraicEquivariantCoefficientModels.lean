/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EquivariantCharacterLineModels
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The actual character polynomial and Laurent coefficient action

The polynomial generator acts by the native first-Chern operation of
character one. Localization uses the actual Laurent polynomial algebra,
whose localization at X is completed Mathlib. Equivariant classes are
genuine native stack-Chow classes; the coefficient extension is tensor
product over this prescribed polynomial action.

Reference: Graber--Pandharipande alg-geom/9708001v2, equation(1).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.AlgebraicEquivariantCoefficientModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open AlgebraicWeightBundleModels AlgebraicEquivariantChowModels EquivariantCharacterLineModels
open StackCycleRelations StackChowGroups
open scoped DirectSum TensorProduct

variable {X : Over base} [ModObj Gm X] (Q : EquivariantSource X)
  (D : CycleConstructionData base (FiniteTypeArtin ℂ)) (K : KreschPresentation D)

def characterOne : Character Gm where
  map := 𝟙 Gm
  hom := inferInstance

abbrev GradedChow := DirectSum ℤ (EquivariantChow D K Q)

-- The graded Kresch tensor groups have large dependent instance conversions.
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The generator's action is the actual character-one zero-section Chern cap. -/
def characterCap (C : CharacterChernData Q D K characterOne) :
    GradedChow Q D K →ₗ[ℚ] GradedChow Q D K :=
  DirectSum.toModule (M := EquivariantChow D K Q) ℚ ℤ (GradedChow Q D K) (fun (i : ℤ) =>
    (DirectSum.lof ℚ ℤ (EquivariantChow D K Q) (i-1)).comp (characterFirstChern Q D K C i))

-- These native group instances are cached to avoid repeatedly unfolding the Kresch presentations.
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The native additive group on the literal sum of equivariant Chow groups. -/
instance gradedGroup : AddCommGroup (GradedChow Q D K) :=
  inferInstanceAs (AddCommGroup (DirectSum ℤ (EquivariantChow D K Q)))

-- This local bound is for the same native graded module-instance conversion.
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The native rational module on the literal sum of Chow groups. -/
instance gradedModule : Module ℚ (GradedChow Q D K) :=
  inferInstanceAs (Module ℚ (DirectSum ℤ (EquivariantChow D K Q)))

-- Cache the large dependent native scalar-instance search locally.
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Both rational scalar actions are the same native module action. -/
instance gradedScalarTower : IsScalarTower ℚ ℚ (GradedChow Q D K) where
  smul_assoc r s a := by
    change (r*s) • a = r • s • a
    exact mul_smul r s a

-- This is the same native scalar-instance search, with no new algebraic data.
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Rational scalar multiplication commutes with itself. -/
instance gradedScalarComm : SMulCommClass ℚ ℚ (GradedChow Q D K) where
  smul_comm r s a := by
    calc
      r • (s • a) = (r*s) • a := (mul_smul r s a).symm
      _ = (s*r) • a := by rw [mul_comm]
      _ = s • (r • a) := mul_smul s r a

-- Cache the actual native End algebra before elaborating algebra-hom types.
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The endomorphism algebra uses precisely the original rational scalar action. -/
instance gradedEndAlgebra : Algebra ℚ (Module.End ℚ (GradedChow Q D K)) :=
  Module.End.instAlgebra ℚ ℚ (GradedChow Q D K)

-- The native End algebra uses the cached group/module instances above.
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Polynomial coefficients evaluate their actual generator at that Chern operator. -/
def polynomialAction (C : CharacterChernData Q D K characterOne) :
    Polynomial ℚ →ₐ[ℚ] Module.End ℚ (GradedChow Q D K) :=
  Polynomial.aeval (characterCap Q D K C)

/-- No independent polynomial module structure is supplied. -/
@[instance_reducible] def polynomialModule (C : CharacterChernData Q D K characterOne) :
    Module (Polynomial ℚ) (GradedChow Q D K) :=
  Module.compHom (GradedChow Q D K) (polynomialAction Q D K C).toRingHom

/-- The coefficient ring `ℚ[X, X⁻¹]` of Laurent polynomials over `ℚ`: the localization of `ℚ[X]`
obtained by inverting `X` (`LaurentPolynomial.isLocalization`). -/
abbrev Coefficients := LaurentPolynomial ℚ

/-- The actual localized equivariant module, via extension along X to T. -/
abbrev LocalizedChow (C : CharacterChernData Q D K characterOne) :=
  letI := polynomialModule Q D K C
  TensorProduct (Polynomial ℚ) Coefficients (GradedChow Q D K)

/-- The native coefficient extension of a genuine graded class. -/
def localize (C : CharacterChernData Q D K characterOne) (a : GradedChow Q D K) :
    LocalizedChow Q D K C :=
  letI := polynomialModule Q D K C
  (1 : Coefficients) ⊗ₜ[Polynomial ℚ] a

end MathlibExt.AlgebraicGeometry.AlgebraicEquivariantCoefficientModels

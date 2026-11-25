/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoalgebraNative
import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping
import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CyclicAlternatization
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Integral Chevalley–Eilenberg values and enveloping projectivity

The commutator Lie algebra of two-by-two integer matrices gives nonzero
boundary values and distinguishes the native tensor sign and the order of
regular coefficient multiplication. Homogeneous involution values use the
canonical exterior-power theorem. Enveloping terms retain projectivity
from the underlying Lie module, in independent scalar and carrier universes.
The integral full alternatization has factors two and three in degrees one and two.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory
open scoped TensorProduct ModuleCat.UniverseTensor

universe u v

namespace MathlibExtTest.Algebra.Homology.ChevalleyEilenbergExport

section Projectivity

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]
  [Module.Projective R L]

/-- Every native enveloping term is projective from the original Lie-module hypothesis. -/
example (n : ℕ) :
    Module.Projective (UniversalEnvelopingAlgebra R L)
      ((ChevalleyEilenberg.envelopingComplex R L).X n) := by
  infer_instance

/-- The same hypothesis supplies categorical projectivity at the native working height. -/
example (n : ℕ) :
    CategoryTheory.Projective ((ChevalleyEilenberg.envelopingComplex R L).X n) := by
  infer_instance

end Projectivity

private abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ
private abbrev E := ExteriorAlgebra ℤ Mat

local instance : LieRing Mat := LieRing.ofAssociativeRing
local instance : LieAlgebra ℤ Mat := LieAlgebra.ofAssociativeAlgebra

private abbrev U := UniversalEnvelopingAlgebra ℤ Mat

private def e01 : Mat := !![0, 1; 0, 0]
private def e10 : Mat := !![0, 0; 1, 0]
private def diagonalBracket : Mat := !![1, 0; 0, -1]
private def pairInputs : Fin 2 → Mat := ![e01, e10]

private theorem matrix_bracket : ⁅e01, e10⁆ = diagonalBracket := by
  change e01 * e10 - e10 * e01 = diagonalBracket
  decide

private def oneVector (x : Mat) : ⋀[ℤ]^1 Mat :=
  exteriorPower.ιMulti ℤ 1 (fun _ => x)

private def pair : ⋀[ℤ]^2 Mat := exteriorPower.ιMulti ℤ 2 pairInputs

@[simp]
private theorem oneVector_coe (x : Mat) : (oneVector x : E) = ExteriorAlgebra.ι ℤ x := by
  simp only [oneVector, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]

@[simp]
private theorem pair_coe :
    (pair : E) = ExteriorAlgebra.ι ℤ e01 * ExteriorAlgebra.ι ℤ e10 := by
  simp [pair, pairInputs, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_succ_apply]

private def degreeOneMatrix : E →ₗ[ℤ] Mat :=
  (exteriorPower.oneEquiv ℤ Mat).toLinearMap.comp (exteriorPower.projection ℤ Mat 1)

@[simp]
private theorem degreeOneMatrix_ι (x : Mat) :
    degreeOneMatrix (ExteriorAlgebra.ι ℤ x) = x := by
  change exteriorPower.oneEquiv ℤ Mat
    (exteriorPower.projection ℤ Mat 1 (ExteriorAlgebra.ι ℤ x)) = x
  rw [← oneVector_coe x, exteriorPower.projection_subtype_apply]
  simp only [oneVector, exteriorPower.oneEquiv_ιMulti]

/-- The ordered matrix-unit wedge has the negative diagonal commutator as boundary. -/
private theorem boundary_pair :
    ChevalleyEilenberg.boundary ℤ Mat (pair : E) =
      -ExteriorAlgebra.ι ℤ diagonalBracket := by
  rw [pair_coe, ChevalleyEilenberg.boundary_ι_mul_ι, matrix_bracket]

/-- The concrete exterior boundary is nonzero, detected by its degree-one projection. -/
example : ChevalleyEilenberg.boundary ℤ Mat (pair : E) ≠ 0 := by
  intro hz
  rw [boundary_pair] at hz
  have h := congrArg degreeOneMatrix hz
  have hm : (-diagonalBracket : Mat) = 0 := by
    simpa only [map_neg, degreeOneMatrix_ι, map_zero] using h
  exact (by decide : (-diagonalBracket : Mat) ≠ 0) hm

/-- The actual degree-two differential has the same nonzero ordered value. -/
example :
    (((ChevalleyEilenberg.canonicalChainData ℤ Mat).complex).d 2 1).hom pair =
      -oneVector diagonalBracket := by
  rw [ChevalleyEilenberg.ChainData.complex_d_succ]
  apply Subtype.ext
  change (ChevalleyEilenberg.differential ℤ Mat 1 pair : E) =
    ((-oneVector diagonalBracket : ⋀[ℤ]^1 Mat) : E)
  simpa only [ChevalleyEilenberg.differential_coe, Submodule.coe_neg,
    oneVector_coe] using boundary_pair

/-- A concrete odd homogeneous element uses the canonical named implicit arguments. -/
example :
    CliffordAlgebra.involute (ExteriorAlgebra.ι ℤ e01) =
      -ExteriorAlgebra.ι ℤ e01 := by
  have h := ExteriorAlgebra.involute_of_mem_exteriorPower
    (A := ℤ) (M := Mat) (n := 1) (x := (oneVector e01 : E)) (oneVector e01).property
  simpa only [oneVector_coe, pow_one, neg_one_smul] using h

/-- The nonzero degree-two wedge has even involution sign over the integers. -/
example : CliffordAlgebra.involute (pair : E) = (pair : E) := by
  have h := ExteriorAlgebra.involute_of_mem_exteriorPower
    (A := ℤ) (M := Mat) (n := 2) (x := (pair : E)) pair.property
  simpa only [pow_two, neg_mul_neg, one_mul, one_smul] using h

/-- The odd first factor changes the negative CE boundary into a positive tensor term. -/
private theorem tensorBoundary_pair :
    ChevalleyEilenberg.tensorBoundary ℤ Mat
        (ExteriorAlgebra.ι ℤ e01 ⊗ₜ[ℤ] (pair : E)) =
      ExteriorAlgebra.ι ℤ e01 ⊗ₜ[ℤ] ExteriorAlgebra.ι ℤ diagonalBracket := by
  rw [ChevalleyEilenberg.tensorBoundary_tmul, ChevalleyEilenberg.boundary_ι,
    boundary_pair, CliffordAlgebra.involute_ι]
  simp only [TensorProduct.zero_tmul, zero_add, TensorProduct.neg_tmul,
    TensorProduct.tmul_neg, neg_neg]

private def tensorMatrixValue : E ⊗[ℤ] E →ₗ[ℤ] Mat :=
  (TensorProduct.lift ((Algebra.lmul ℤ Mat).toLinearMap)).comp
    (TensorProduct.map degreeOneMatrix degreeOneMatrix)

private theorem tensorMatrixValue_tmul (a b : E) :
    tensorMatrixValue (a ⊗ₜ[ℤ] b) = degreeOneMatrix a * degreeOneMatrix b := by
  let m : Mat ⊗[ℤ] Mat →ₗ[ℤ] Mat :=
    TensorProduct.lift ((Algebra.lmul ℤ Mat).toLinearMap)
  let p : E ⊗[ℤ] E →ₗ[ℤ] Mat ⊗[ℤ] Mat :=
    TensorProduct.map degreeOneMatrix degreeOneMatrix
  have hp : p (a ⊗ₜ[ℤ] b) = degreeOneMatrix a ⊗ₜ[ℤ] degreeOneMatrix b :=
    TensorProduct.map_tmul degreeOneMatrix degreeOneMatrix a b
  have hm : m (degreeOneMatrix a ⊗ₜ[ℤ] degreeOneMatrix b) =
      degreeOneMatrix a * degreeOneMatrix b :=
    TensorProduct.lift.tmul (f' := (Algebra.lmul ℤ Mat).toLinearMap) _ _
  change m (p (a ⊗ₜ[ℤ] b)) = _
  exact (congrArg m hp).trans hm

private theorem tensor_pair_ne_zero :
    (ExteriorAlgebra.ι ℤ e01 ⊗ₜ[ℤ] ExteriorAlgebra.ι ℤ diagonalBracket : E ⊗[ℤ] E) ≠ 0 := by
  intro hz
  have h := congrArg tensorMatrixValue hz
  rw [tensorMatrixValue_tmul, degreeOneMatrix_ι, degreeOneMatrix_ι, map_zero] at h
  exact (by decide : e01 * diagonalBracket ≠ (0 : Mat)) h

private def nativeInput : (ChevalleyEilenberg.nativeTensorComplex ℤ Mat).X 3 :=
  (ExteriorAlgebra.tensorDegreeι ℤ Mat 1 2 3 (by decide)).hom
    (oneVector e01 ⊗ₜ[ℤ] pair)

private theorem nativeInput_realize :
    (ExteriorAlgebra.tensorDegreeRealize ℤ Mat 3).hom nativeInput =
      ExteriorAlgebra.ι ℤ e01 ⊗ₜ[ℤ] (pair : E) := by
  have h := congrArg (fun f => f.hom (oneVector e01 ⊗ₜ[ℤ] pair))
    (ExteriorAlgebra.tensorDegreeι_realize ℤ Mat 1 2 3 (by decide))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    TensorProduct.map_tmul, Submodule.subtype_apply, nativeInput, oneVector_coe] using h

/-- The native total differential realizes the nonzero odd-factor tensor value. -/
private theorem nativeDifferential_pair :
    (ExteriorAlgebra.tensorDegreeRealize ℤ Mat 2).hom
        (((ChevalleyEilenberg.nativeTensorComplex ℤ Mat).d 3 2).hom nativeInput) =
      ExteriorAlgebra.ι ℤ e01 ⊗ₜ[ℤ] ExteriorAlgebra.ι ℤ diagonalBracket := by
  have h := congrArg (fun f => f.hom nativeInput)
    (ChevalleyEilenberg.nativeTensorDifferential_realize ℤ Mat 2)
  change (ExteriorAlgebra.tensorDegreeRealize ℤ Mat 2).hom
      (((ChevalleyEilenberg.nativeTensorComplex ℤ Mat).d 3 2).hom nativeInput) =
    ChevalleyEilenberg.tensorBoundary ℤ Mat
      ((ExteriorAlgebra.tensorDegreeRealize ℤ Mat 3).hom nativeInput) at h
  rw [nativeInput_realize, tensorBoundary_pair] at h
  exact h

/-- The actual native tensor differential is nonzero on this antidiagonal summand. -/
example : ((ChevalleyEilenberg.nativeTensorComplex ℤ Mat).d 3 2).hom nativeInput ≠ 0 := by
  intro hz
  let r : (ChevalleyEilenberg.nativeTensorComplex ℤ Mat).X 2 →ₗ[ℤ] E ⊗[ℤ] E :=
    (ExteriorAlgebra.tensorDegreeRealize ℤ Mat 2).hom
  have hValue : r (((ChevalleyEilenberg.nativeTensorComplex ℤ Mat).d 3 2).hom nativeInput) =
      ExteriorAlgebra.ι ℤ e01 ⊗ₜ[ℤ] ExteriorAlgebra.ι ℤ diagonalBracket :=
    nativeDifferential_pair
  exact tensor_pair_ne_zero (hValue.symm.trans ((congrArg r hz).trans r.map_zero))

/-- Matrix Lie coefficients supply the base projectivity needed by the enveloping term. -/
example : Module.Projective U ((ChevalleyEilenberg.envelopingComplex ℤ Mat).X 2) := by
  infer_instance

private def evaluate : U →ₐ[ℤ] Mat :=
  UniversalEnvelopingAlgebra.lift ℤ (LieHom.id : Mat →ₗ⁅ℤ⁆ Mat)

@[simp]
private theorem evaluate_ι (x : Mat) : evaluate (UniversalEnvelopingAlgebra.ι ℤ x) = x :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℤ (LieHom.id : Mat →ₗ⁅ℤ⁆ Mat) x

/-- Positive right multiplication gives the lower diagonal unit, distinguishing the map order. -/
example :
    evaluate (ChevalleyEilenberg.envelopingZeroEquiv ℤ Mat
      (((ChevalleyEilenberg.envelopingComplex ℤ Mat).d 1 0).hom
        (oneVector e01 ⊗ₜ[ℤ]
          (UniversalEnvelopingAlgebra.ι ℤ e10 : ChevalleyEilenberg.regularCoefficients ℤ Mat)))) =
      !![0, 0; 0, 1] := by
  rw [oneVector, ChevalleyEilenberg.envelopingComplex_d_one,
    ChevalleyEilenberg.envelopingZeroEquiv_tmul, exteriorPower.zeroEquiv_ιMulti]
  change evaluate ((1 : ℤ) •
    (UniversalEnvelopingAlgebra.ι ℤ e10 * UniversalEnvelopingAlgebra.ι ℤ e01 : U)) = _
  have hUnit : (1 : ℤ) •
      (UniversalEnvelopingAlgebra.ι ℤ e10 * UniversalEnvelopingAlgebra.ι ℤ e01 : U) =
      UniversalEnvelopingAlgebra.ι ℤ e10 * UniversalEnvelopingAlgebra.ι ℤ e01 :=
    one_smul ℤ _
  have hValue : evaluate (UniversalEnvelopingAlgebra.ι ℤ e10 *
      UniversalEnvelopingAlgebra.ι ℤ e01) = !![0, 0; 0, 1] := by
    simpa only [map_mul, evaluate_ι] using
      (show e10 * e01 = !![0, 0; 0, 1] by decide)
  exact (congrArg evaluate hUnit).trans hValue

/-- The one-permutation integral tail has the original ordered matrix-unit representative. -/
private theorem integral_tail_pair :
    ChevalleyEilenberg.cyclicTailSum ℤ Mat 1 pairInputs =
      ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative ℤ Mat 1
        (e01 ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ (fun _ : Fin 1 => e10)) := by
  classical
  have hfirst : pairInputs 0 = e01 := rfl
  have htail : (fun j : Fin 1 => pairInputs j.succ) = (fun _ : Fin 1 => e10) := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl
  rw [ChevalleyEilenberg.cyclicTailSum, Finset.sum_eq_single (1 : Equiv.Perm (Fin 1))]
  · simpa only [map_one, one_smul, Equiv.Perm.one_apply, hfirst] using
      congrArg (fun f : Fin 1 → Mat =>
        ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative ℤ Mat 1
          (e01 ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ f)) htail
  · intro σ _ hne
    exact False.elim (hne (Subsingleton.elim _ _))
  · simp

/-- The full integral sum is twice that representative, without rational normalization. -/
example :
    ChevalleyEilenberg.cyclicFullExterior ℤ Mat 1 pair =
      (2 : ℕ) • ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative ℤ Mat 1
        (e01 ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ (fun _ : Fin 1 => e10)) := by
  have h := ChevalleyEilenberg.cyclicFullExterior_eq_factor_tail ℤ Mat 1 pairInputs
  change ChevalleyEilenberg.cyclicFullExterior ℤ Mat 1 pair =
    2 • ChevalleyEilenberg.cyclicTailSum ℤ Mat 1 pairInputs at h
  rw [integral_tail_pair] at h
  exact h

/-- Three input factors give integral factor three, distinguishing it from factorial scaling. -/
example :
    ChevalleyEilenberg.cyclicFullExterior ℤ Mat 2
        (exteriorPower.ιMulti ℤ 3 ![e01, e10, (!![1, 0; 0, 0] : Mat)]) =
      (3 : ℕ) • ChevalleyEilenberg.cyclicTailSum ℤ Mat 2
        ![e01, e10, (!![1, 0; 0, 0] : Mat)] := by
  exact ChevalleyEilenberg.cyclicFullExterior_eq_factor_tail ℤ Mat 2
    ![e01, e10, (!![1, 0; 0, 0] : Mat)]

end MathlibExtTest.Algebra.Homology.ChevalleyEilenbergExport

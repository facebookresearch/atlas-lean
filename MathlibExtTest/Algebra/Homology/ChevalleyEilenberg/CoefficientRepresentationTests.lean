/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Category.LieModuleCat.UniversalEnveloping
import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientFunctor
import MathlibExt.Algebra.Homology.ChevalleyEilenberg.LieNaturality
import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Transport
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Adjoint matrix coefficients, coinvariants and enveloping actions

Integer two-by-two matrices have a nonzero commutator. Its coefficient homology
class vanishes, while trace detects a nonzero identity-matrix class. Doubling
the coefficients acts nontrivially on that homology class. The representation
in the universal enveloping algebra retains the original nonzero Lie action.
-/

noncomputable section

open CategoryTheory ChevalleyEilenberg
open scoped TensorProduct

namespace MathlibExtTest.CoefficientRepresentation

private abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ
local instance : LieRing Mat := LieRing.ofAssociativeRing
local instance : LieAlgebra ℤ Mat := LieAlgebra.ofAssociativeAlgebra
local instance : LieRingModule Mat Mat := lieRingSelfModule
local instance : LieModule ℤ Mat Mat := lieAlgebraSelfModule
private def e01 : Mat := !![0, 1; 0, 0]
private def e10 : Mat := !![0, 0; 1, 0]
private def diagonal : Mat := !![1, 0; 0, -1]
private lemma matrixBracket : ⁅e01, e10⁆ = diagonal := by
  change e01 * e10 - e10 * e01 = diagonal
  decide

local instance : LieRingModule Mat ℤ where
  bracket _ _ := 0
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  leibniz_lie _ _ _ := by simp
local instance : LieModule ℤ Mat ℤ where
  smul_lie _ _ _ := by simp
  lie_smul _ _ _ := by simp
local instance : LieModule.IsTrivial Mat ℤ := ⟨fun _ _ => rfl⟩

private def traceMap : Mat →ₗ⁅ℤ,Mat⁆ ℤ where
  __ := Matrix.traceLinearMap (Fin 2) ℤ
  map_lie' {x m} := by
    change Matrix.trace (x * m - m * x) = 0
    rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
private abbrev K := coefficientComplex ℤ Mat Mat
private def cl (m : Mat) : K.homology 0 := K.isoHomologyι₀.inv
  (K.pOpcycles 0 (exteriorPower.ιMulti ℤ 0 Fin.elim0 ⊗ₜ[ℤ] m))
private def readHomology : K.homology 0 →ₗ[ℤ] ℤ :=
  (coefficientHomologyZeroTrivialLinearEquiv ℤ Mat ℤ).toLinearMap.comp
    (HomologicalComplex.homologyMap (coefficientComplexMap ℤ Mat Mat traceMap) 0).hom

private lemma read_class (m : Mat) : readHomology (cl m) = Matrix.trace m := by
  change coefficientHomologyZeroTrivialLinearEquiv ℤ Mat ℤ
    ((HomologicalComplex.homologyMap (coefficientComplexMap ℤ Mat Mat traceMap) 0).hom
      (cl m)) = Matrix.trace m
  have h := coefficientHomologyMap_zero_class ℤ Mat Mat traceMap m
  exact (congrArg (coefficientHomologyZeroTrivialLinearEquiv ℤ Mat ℤ) h).trans
    (coefficientHomologyZeroTrivialLinearEquiv_class ℤ Mat ℤ (traceMap m))

example : cl diagonal = 0 := by
  have h := coefficientHomologyZero_lie_class ℤ Mat Mat e01 e10
  exact (congrArg cl matrixBracket).symm.trans h

private lemma read_identity : readHomology (cl (1 : Mat)) = 2 :=
  (read_class 1).trans (by decide : Matrix.trace (1 : Mat) = (2 : ℤ))
example : readHomology (cl (1 : Mat)) = 2 := read_identity
example : cl (1 : Mat) ≠ 0 := by
  intro hz
  exact (by decide : (2 : ℤ) ≠ 0)
    (read_identity.symm.trans ((congrArg readHomology hz).trans readHomology.map_zero))

private def doubled : Mat →ₗ⁅ℤ,Mat⁆ Mat := (2 : ℤ) • LieModuleHom.id
private def homologyDouble : K.homology 0 ⟶ K.homology 0 :=
  HomologicalComplex.homologyMap (coefficientComplexMap ℤ Mat Mat doubled) 0
private lemma doubled_value : readHomology (homologyDouble.hom (cl (1 : Mat))) = 4 := by
  have h := coefficientHomologyMap_zero_class ℤ Mat Mat doubled (1 : Mat)
  exact (congrArg readHomology h).trans
    ((read_class (doubled (1 : Mat))).trans (by decide))
example : readHomology (homologyDouble.hom (cl (1 : Mat))) = 4 := doubled_value
example : homologyDouble ≠ 𝟙 (K.homology 0) := by
  intro h
  have hp := congrArg
    (fun f : K.homology 0 ⟶ K.homology 0 => readHomology (f.hom (cl (1 : Mat)))) h
  have h42 : (4 : ℤ) = 2 := doubled_value.symm.trans (hp.trans read_identity)
  exact (by decide : (4 : ℤ) ≠ 2) h42

private abbrev M : LieModuleCat.{0} ℤ Mat := LieModuleCat.of ℤ Mat Mat
private abbrev U := UniversalEnvelopingAlgebra ℤ Mat
example : LieModuleCat.UniversalEnveloping.representation ℤ Mat M
    (UniversalEnvelopingAlgebra.ι ℤ e01) e10 = diagonal :=
  (LieModuleCat.UniversalEnveloping.representation_ι ℤ Mat M e01 e10).trans matrixBracket
example : LieModuleCat.UniversalEnveloping.representation ℤ Mat M
    (UniversalEnvelopingAlgebra.ι ℤ e01) e10 ≠ 0 := by
  have h := LieModuleCat.UniversalEnveloping.representation_ι ℤ Mat M e01 e10
  intro hz
  exact (by decide : diagonal ≠ 0) ((h.trans matrixBracket).symm.trans hz)
example : (LieModuleCat.UniversalEnveloping.unitIso ℤ Mat M).hom e10 = e10 :=
  LieModuleCat.UniversalEnveloping.unitIso_hom_apply ℤ Mat M e10

private def categoryDouble : M ⟶ M := LieModuleCat.ofHom doubled
example : (LieModuleCat.UniversalEnveloping.representMap ℤ Mat categoryDouble).hom e10 =
    (2 : ℤ) • e10 :=
  (LieModuleCat.UniversalEnveloping.representMap_apply ℤ Mat categoryDouble e10).trans rfl
example : (LieModuleCat.UniversalEnveloping.representMap ℤ Mat categoryDouble).hom e10 ≠ 0 := by
  have h := LieModuleCat.UniversalEnveloping.representMap_apply ℤ Mat categoryDouble e10
  intro hz
  exact (by decide : ((2 : ℤ) • e10 : Mat) ≠ 0) (h.symm.trans hz)

example : ((coefficientHomologyZeroNatIso ℤ Mat).app M).hom (cl e10) =
    ULift.up (LieSubmodule.Quotient.mk
      (N := ⁅(⊤ : LieIdeal ℤ Mat), (⊤ : LieSubmodule ℤ Mat M)⁆) e10) :=
  coefficientHomologyZeroNatIso_class ℤ Mat M e10

private abbrev T : LieModuleCat.{0} ℤ Mat := LieModuleCat.of ℤ Mat ℤ
private def collapseCoefficient : T →ₗ⁅ℤ,Mat⁆ LieModuleCat.restrictObj
    (0 : Mat →ₗ⁅ℤ⁆ Mat) T where
  toLinearMap := LinearMap.id
  map_lie' := by
    intro x m
    change (0 : ℤ) = 0
    rfl
example : coefficientLieAmbientMap ℤ Mat (0 : Mat →ₗ⁅ℤ⁆ Mat) T T collapseCoefficient
    (ExteriorAlgebra.ι ℤ e01 ⊗ₜ[ℤ] (1 : ℤ)) = 0 := by
  rw [coefficientLieAmbientMap_tmul]
  simp

private abbrev canonical := (canonicalChainData ℤ Mat).complex
private def signedCoordinates (n : ℕ) : canonical.X n ≅ chainObject ℤ Mat n :=
  (-1 : ℤˣ) • Iso.refl _
example : ((ChainData.ofComplexIso ℤ Mat canonical signedCoordinates).hom.f 1).hom
    (exteriorPower.ιMulti ℤ 1 (fun _ => e01)) =
      -exteriorPower.ιMulti ℤ 1 (fun _ => e01) := by
  rw [ChainData.ofComplexIso_hom_f]
  simp [signedCoordinates]

end MathlibExtTest.CoefficientRepresentation

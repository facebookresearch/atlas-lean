/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Category.CommAlgCat.Free
import MathlibExt.Algebra.Category.CommAlgCat.Cotangent
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Tactic.NormNum

/-!
# Polynomial adjunction and augmented cotangent generators

A polynomial variable is evaluated at three through the actual free/forget
adjunction. The polynomial map X ↦ 2X is a nonidentity map between two
augmentations over the same algebra. Its cotangent map sends dX to d(2X).
The universal cotangent correspondence constructs the derivation taking X to
one, and its associated linear map detects a nonzero differential generator.
-/

noncomputable section

open CategoryTheory

namespace MathlibExtTest.CotangentAdjunction

private abbrev Z : CommAlgCat.{0} ℤ := CommAlgCat.of ℤ ℤ
private def evalThree : (CommAlgCat.free.{0, 0} ℤ).obj (Fin 1) ⟶ Z :=
  CommAlgCat.ofHom (MvPolynomial.aeval (fun _ : Fin 1 => (3 : ℤ)))

example :
    ((CommAlgCat.freeForgetAdjunction.{0, 0} ℤ).homEquiv (Fin 1) Z evalThree) 0 = 3 := by
  rw [CommAlgCat.freeForgetAdjunction_homEquiv_apply]
  change MvPolynomial.aeval (fun _ : Fin 1 => (3 : ℤ)) (MvPolynomial.X 0) = 3
  exact MvPolynomial.aeval_X _ _

example :
    ((CommAlgCat.freeCounit.{0, 0} ℤ).app Z).hom (MvPolynomial.X (3 : ℤ)) = 3 :=
  CommAlgCat.freeCounit_app_X (k := ℤ) Z 3

example : (CommAlgCat.free.{0, 0} ℤ).IsLeftAdjoint := inferInstance

private abbrev P := MvPolynomial (Fin 1) ℤ
private abbrev A : CommAlgCat.{0} ℤ := CommAlgCat.of ℤ P
private abbrev point : Over A := Over.mk (𝟙 A)
private def doublePolynomial : A ⟶ A :=
  CommAlgCat.ofHom (MvPolynomial.aeval (fun i : Fin 1 => (2 : P) * MvPolynomial.X i))
private abbrev doublePoint : Over A := Over.mk doublePolynomial
private def doubleToPoint : doublePoint ⟶ point :=
  Over.homMk doublePolynomial (Category.comp_id _)

example :
    ((CommAlgCat.cotangentFunctor ℤ A).map doubleToPoint).hom
        (CommAlgCat.cotangentTensor ℤ A doublePoint 1 (MvPolynomial.X 0)) =
      CommAlgCat.cotangentTensor ℤ A point 1 ((2 : P) * MvPolynomial.X 0) := by
  change (CommAlgCat.cotangentMap ℤ A doubleToPoint).hom _ = _
  exact (CommAlgCat.cotangentMap_tensor ℤ A doubleToPoint 1 (MvPolynomial.X 0)).trans
    (congrArg (CommAlgCat.cotangentTensor ℤ A point 1)
      (MvPolynomial.aeval_X (fun i : Fin 1 => (2 : P) * MvPolynomial.X i) 0))

section Universal

private abbrev coefficients : ModuleCat.{0} A := ModuleCat.of A P
local instance : Module point.left coefficients :=
  Module.compHom coefficients point.hom.hom.toRingHom
local instance : Module ℤ coefficients :=
  Module.compHom coefficients (algebraMap ℤ A)

private def dx : CommAlgCat.CotangentDerivations ℤ A point coefficients := by
  letI := IsScalarTower.of_compHom ℤ point.left coefficients
  change Derivation ℤ P coefficients
  exact MvPolynomial.mkDerivation ℤ (fun _ : Fin 1 => (1 : coefficients))

private lemma dx_X :
    CommAlgCat.cotangentDerivationValue ℤ A point coefficients dx (MvPolynomial.X 0) = 1 := by
  letI := IsScalarTower.of_compHom ℤ point.left coefficients
  change (MvPolynomial.mkDerivation ℤ (fun _ : Fin 1 => (1 : coefficients)))
    (MvPolynomial.X 0) = 1
  exact MvPolynomial.mkDerivation_X ℤ (fun _ : Fin 1 => (1 : coefficients)) (0 : Fin 1)

private def detect : CommAlgCat.cotangent ℤ A point →ₗ[A] coefficients :=
  (CommAlgCat.cotangentHomEquivDerivation ℤ A point coefficients).symm dx

example : detect (CommAlgCat.cotangentTensor ℤ A point 1 (MvPolynomial.X 0)) = 1 := by
  have h := congrArg
    (fun D => CommAlgCat.cotangentDerivationValue ℤ A point coefficients D (MvPolynomial.X 0))
    ((CommAlgCat.cotangentHomEquivDerivation ℤ A point coefficients).apply_symm_apply dx)
  exact (CommAlgCat.cotangentHomEquivDerivation_apply ℤ A point coefficients detect
    (MvPolynomial.X 0)).symm.trans (h.trans dx_X)

example : CommAlgCat.cotangentTensor ℤ A point 1 (MvPolynomial.X 0) ≠ 0 := by
  intro hz
  have h := congrArg detect hz
  have hv := (CommAlgCat.cotangentHomEquivDerivation_apply ℤ A point coefficients detect
    (MvPolynomial.X 0)).symm
  have hd := congrArg
    (fun D => CommAlgCat.cotangentDerivationValue ℤ A point coefficients D (MvPolynomial.X 0))
    ((CommAlgCat.cotangentHomEquivDerivation ℤ A point coefficients).apply_symm_apply dx)
  have h10 : (1 : coefficients) = 0 :=
    (hv.trans (hd.trans dx_X)).symm.trans (h.trans detect.map_zero)
  exact (by norm_num : (1 : P) ≠ 0) h10

end Universal

end MathlibExtTest.CotangentAdjunction

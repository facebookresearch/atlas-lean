/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.FiniteFactorIso

/-!
# Finite tensor-factor Hom comparisons

The coefficient example has an infinite Hom source and a rank-one tensor
factor. The cochain examples have arbitrary Hom complexes, compute the
source-index sign at singleton support intervals, and use the zero complex
at an empty interval.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
open CochainComplex.ModuleTensor
open scoped TensorProduct

-- The categorical Iso retains the original coefficient map on concrete values.
example :
    ((ModuleCat.finiteProjectiveTensorFactorHomTensorIso ℤ
      (ModuleCat.of ℤ (ℤ → ℤ)) (ModuleCat.of ℤ ℤ) (ModuleCat.of ℤ ℤ)).hom.hom
        ((LinearMap.proj (0 : ℤ)) ⊗ₜ[ℤ] (3 : ℤ))) (fun _ => (2 : ℤ)) =
      (2 : ℤ) ⊗ₜ[ℤ] (3 : ℤ) := by
  rw [ModuleCat.finiteProjectiveTensorFactorHomTensorIso_hom,
    TensorProduct.rTensorHomToHomRTensor_apply]
  rfl

-- Rank zero remains a valid finite-projective tensor factor.
example (f : (ℤ → ℤ) →ₗ[ℤ] ℤ) (x : ℤ → ℤ) :
    (TensorProduct.homTensorFiniteFactorEquiv ℤ (ℤ → ℤ) ℤ (Fin 0 → ℤ)
      (f ⊗ₜ[ℤ] (0 : Fin 0 → ℤ))) x = 0 := by
  change (TensorProduct.rTensorHomToHomRTensor (.id ℤ) (ℤ → ℤ) ℤ (Fin 0 → ℤ)
    (f ⊗ₜ[ℤ] (0 : Fin 0 → ℤ))) x = 0
  rw [TensorProduct.rTensorHomToHomRTensor_apply, TensorProduct.tmul_zero]

universe u v

variable (R : Type u) [CommRing R]

section SingletonSupport

variable (P J U : CochainComplex (ModuleCat.{v} R) ℤ)
  [∀ b : ℤ, CategoryTheory.Projective (U.X b)] [∀ b : ℤ, Module.Finite R (U.X b)]

-- The singleton interval [0,0] gives the original unsigned pure value.
example (hUlo : ∀ b : ℤ, b < 0 → IsZero (U.X b))
    (hUhi : ∀ b : ℤ, 0 < b → IsZero (U.X b))
    (f : Cochain P J 0) (u : U.X 0) (x : P.X (-1)) :
    ((((finiteFactorHomTensorIso R P J U 0 0 hUlo hUhi).hom.f 0).hom
      (mkAt R (linearComplex R P J) U 0 0 0 (by decide) f u)).v
        (-1) (-1) (by decide)).hom x =
      mkAt R J U (-1) 0 (-1) (by decide) ((f.v (-1) (-1) (by decide)).hom x) u := by
  rw [finiteFactorHomTensorIso_hom]
  change ((((homTensorDegree R P J U 0).hom
    (mkAt R (linearComplex R P J) U 0 0 0 (by decide) f u)).v
      (-1) (-1) (by decide)).hom x) = _
  simpa using homTensorDegree_mk_v' R P J U 0 0 0 (by decide) f u
    (-1) (-1) (-1) (by decide) (by decide) x

-- At support [1,1], source degree -1 contributes a negative sign.
example (hUlo : ∀ b : ℤ, b < 1 → IsZero (U.X b))
    (hUhi : ∀ b : ℤ, 1 < b → IsZero (U.X b))
    (f : Cochain P J 0) (u : U.X 1) (x : P.X (-1)) :
    ((((finiteFactorHomTensorIso R P J U 1 1 hUlo hUhi).hom.f 1).hom
      (mkAt R (linearComplex R P J) U 0 1 1 (by decide) f u)).v
        (-1) 0 (by decide)).hom x =
      -mkAt R J U (-1) 1 0 (by decide) ((f.v (-1) (-1) (by decide)).hom x) u := by
  rw [finiteFactorHomTensorIso_hom]
  change ((((homTensorDegree R P J U 1).hom
    (mkAt R (linearComplex R P J) U 0 1 1 (by decide) f u)).v
      (-1) 0 (by decide)).hom x) = _
  simpa [Units.smul_def] using homTensorDegree_mk_v' R P J U 1 0 1 (by decide) f u
    (-1) (-1) 0 (by decide) (by decide) x

end SingletonSupport

private abbrev zeroFactor : CochainComplex (ModuleCat.{v} R) ℤ :=
  HomologicalComplex.zero

private theorem zeroFactor_isZero (b : ℤ) : IsZero ((zeroFactor R).X b) :=
  isZero_zero _

private instance zeroFactor_projective (b : ℤ) :
    CategoryTheory.Projective ((zeroFactor R).X b) :=
  (zeroFactor_isZero R b).projective

private instance zeroFactor_finite (b : ℤ) : Module.Finite R ((zeroFactor R).X b) := by
  let : Subsingleton ((zeroFactor R).X b) :=
    ModuleCat.subsingleton_of_isZero (zeroFactor_isZero R b)
  let : Fintype ((zeroFactor R).X b) := Fintype.ofSubsingleton 0
  infer_instance

-- An empty interval is accepted for the actual zero tensor factor.
example (P J : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
    (z : Cochain P (complexAt R J (zeroFactor R)) n) :
    ((finiteFactorHomTensorIso R P J (zeroFactor R) 1 0
      (fun b _ => zeroFactor_isZero R b)
      (fun b _ => zeroFactor_isZero R b)).inv.f n).hom z = 0 := by
  have h := LinearMap.congr_fun
    (finiteFactorHomTensorIso_inv_f R P J (zeroFactor R) 1 0
      (fun b _ => zeroFactor_isZero R b)
      (fun b _ => zeroFactor_isZero R b) n) z
  simpa only [homTensorFiniteFactorInverseDegree,
    Finset.Icc_eq_empty_of_lt (by decide : (0 : ℤ) < 1), Finset.sum_empty,
    LinearMap.zero_apply] using h

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

public import MathlibExt.Algebra.Category.ModuleCat.TorFlat

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u

namespace MathlibExtTest.Algebra.Category.ModuleCat.TorFlat

variable {R : Type u} [CommRing R]

/-! ## Exact orientation and positive degrees -/

example (A D : ModuleCat.{u} R) [Module.Flat R A] (p : ℕ) :
    IsZero (((CategoryTheory.Tor (ModuleCat.{u} R) (p + 1)).obj A).obj D) :=
  CategoryTheory.isZero_Tor_succ_of_flat_left A D p

example (A D : ModuleCat.{u} R) [Module.Flat R A] :
    IsZero (((CategoryTheory.Tor (ModuleCat.{u} R) 1).obj A).obj D) :=
  CategoryTheory.isZero_Tor_succ_of_flat_left A D 0

example (A D : ModuleCat.{u} R) [CategoryTheory.Projective D] (p : ℕ) :
    IsZero (((CategoryTheory.Tor (ModuleCat.{u} R) (p + 1)).obj A).obj D) :=
  CategoryTheory.isZero_Tor_succ_of_projective (ModuleCat.{u} R) A D p

/-! ## Concrete coefficient and zero-object boundaries -/

example (𝕜 : Type u) [Field 𝕜] (D : ModuleCat.{u} 𝕜) (p : ℕ) :
    IsZero (((CategoryTheory.Tor (ModuleCat.{u} 𝕜) (p + 1)).obj
      (ModuleCat.of 𝕜 𝕜)).obj D) :=
  CategoryTheory.isZero_Tor_succ_of_flat_left (ModuleCat.of 𝕜 𝕜) D p

example (D : ModuleCat.{0} ℤ) (p : ℕ) :
    IsZero (((CategoryTheory.Tor (ModuleCat.{0} ℤ) (p + 1)).obj
      (ModuleCat.of ℤ ℤ)).obj D) :=
  CategoryTheory.isZero_Tor_succ_of_flat_left (ModuleCat.of ℤ ℤ) D p

private theorem flat_of_isZero (M : ModuleCat.{u} R) (hM : IsZero M) :
    Module.Flat R M := by
  let _ : Subsingleton M := ModuleCat.subsingleton_of_isZero hM
  let e : M ≃ₗ[R] (Fin 0 →₀ R) :=
    LinearEquiv.ofBijective (0 : M →ₗ[R] (Fin 0 →₀ R))
      ⟨fun _ _ _ => Subsingleton.elim _ _,
        fun y => ⟨0, Subsingleton.elim _ y⟩⟩
  exact Module.Flat.of_linearEquiv e

example (D : ModuleCat.{u} R) (p : ℕ) :
    IsZero (((CategoryTheory.Tor (ModuleCat.{u} R) (p + 1)).obj
      (0 : ModuleCat.{u} R)).obj D) := by
  let _ : Module.Flat R (0 : ModuleCat.{u} R) :=
    flat_of_isZero 0 (isZero_zero _)
  exact CategoryTheory.isZero_Tor_succ_of_flat_left 0 D p

example (A : ModuleCat.{u} R) [Module.Flat R A] (p : ℕ) :
    IsZero (((CategoryTheory.Tor (ModuleCat.{u} R) (p + 1)).obj A).obj 0) :=
  CategoryTheory.isZero_Tor_succ_of_flat_left A 0 p

example (p : ℕ) :
    IsZero (((CategoryTheory.Tor (ModuleCat.{u} R) (p + 1)).obj
      (0 : ModuleCat.{u} R)).obj 0) := by
  let _ : Module.Flat R (0 : ModuleCat.{u} R) :=
    flat_of_isZero 0 (isZero_zero _)
  exact CategoryTheory.isZero_Tor_succ_of_flat_left 0 0 p

/-! ## Finite-biproduct consumption -/

local instance : HasFiniteBiproducts (ModuleCat.{u} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts

example (A : ModuleCat.{u} R) [Module.Flat R A]
    (D : Fin 3 → ModuleCat.{u} R) (p : ℕ) :
    IsZero (⨁ fun i : Fin 3 =>
      ((CategoryTheory.Tor (ModuleCat.{u} R) (p + 1)).obj A).obj (D i)) := by
  rw [IsZero.iff_id_eq_zero]
  apply biproduct.hom_ext'
  intro i
  exact (CategoryTheory.isZero_Tor_succ_of_flat_left A (D i) p).eq_of_src _ _

end MathlibExtTest.Algebra.Category.ModuleCat.TorFlat

end

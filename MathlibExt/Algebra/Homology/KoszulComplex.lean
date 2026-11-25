/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
-- Original authors: @toskua, Avocado
module

public import MathlibExt.LinearAlgebra.ExteriorPower.Contraction
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Koszul complexes of linear functionals

This file constructs the nonnegative Koszul chain complex attached to a
linear functional `x : M →ₗ[R] R`. Its degree-`n` term is the `n`th exterior
power of `M`, and its differential is contraction by `x`, factored through
exterior-power deletion.

The construction is functorial over a fixed base ring.

## Main declarations

* `KoszulComplex.differential`
* `KoszulComplex.differential_comp_differential`
* `KoszulComplex.complex`
* `KoszulComplex.map`
-/

@[expose] public section


noncomputable section

open Function
open CategoryTheory
open scoped TensorProduct

universe u v w

namespace KoszulComplex

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The Koszul differential attached to a linear functional. -/
@[no_expose]
def differential (x : M →ₗ[R] R) (n : ℕ) :
    (⋀[R]^(n + 1) M) →ₗ[R] (⋀[R]^n M) :=
  exteriorPower.contractLeft R M x n

/-- The public Koszul differential is the degree-restricted native contraction. -/
theorem differential_eq_contractLeft (x : M →ₗ[R] R) (n : ℕ) :
    differential R M x n = exteriorPower.contractLeft R M x n := by
  apply LinearMap.ext
  intro a
  rfl

/-- Signed formula for the Koszul differential on a decomposable wedge. -/
theorem differential_apply_ιMulti (x : M →ₗ[R] R) (n : ℕ)
    (a : Fin (n + 1) → M) :
    differential R M x n (exteriorPower.ιMulti R (n + 1) a) =
      ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
        (x (a i) • exteriorPower.ιMulti R n (a ∘ i.succAbove)) :=
  exteriorPower.contractLeft_apply_ιMulti R M x n a

/-- The Koszul differential is evaluation of exterior-power deletion by the
coefficient functional. -/
theorem differential_eq_deletion (x : M →ₗ[R] R) (n : ℕ) :
    differential R M x n =
      (TensorProduct.rid R (⋀[R]^n M)).toLinearMap.comp
        ((TensorProduct.map (LinearMap.id (R := R) (M := (⋀[R]^n M))) x).comp
          (exteriorPower.deletion R M n)) :=
  exteriorPower.contractLeft_eq_deletion R M x n

/-- Successive Koszul differentials compose to zero. -/
theorem differential_comp_differential (x : M →ₗ[R] R) (n : ℕ) :
    (differential R M x n).comp (differential R M x (n + 1)) = 0 := by
  exact exteriorPower.contractLeft_comp_contractLeft R M x n

/-- The nonnegative Koszul chain complex attached to a linear functional. -/
def complex (x : M →ₗ[R] R) :
    ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.of
    (fun n => ModuleCat.of R (⋀[R]^n M))
    (fun n => ModuleCat.ofHom (differential R M x n))
    (fun n => by
      rw [← ModuleCat.ofHom_comp,
        differential_comp_differential R M x n, ModuleCat.ofHom_zero])

/-- The degree-`n` object of the Koszul complex. -/
theorem complex_X (x : M →ₗ[R] R) (n : ℕ) :
    (complex R M x).X n = ModuleCat.of R (⋀[R]^n M) :=
  rfl

/-- The successor differential of the Koszul complex. -/
theorem complex_d_succ (x : M →ₗ[R] R) (n : ℕ) :
    (complex R M x).d (n + 1) n =
      ModuleCat.ofHom (differential R M x n) := by
  simp [complex, ChainComplex.of_d]

/-- Naturality of the Koszul differential over a fixed base ring. -/
theorem differential_naturality
    {N : Type w} [AddCommGroup N] [Module R N]
    (x : M →ₗ[R] R) (y : N →ₗ[R] R) (f : M →ₗ[R] N)
    (hxy : y.comp f = x) (n : ℕ) :
    (differential R N y n).comp (exteriorPower.map (n + 1) f) =
      (exteriorPower.map n f).comp (differential R M x n) :=
  exteriorPower.contractLeft_naturality R M x y f hxy n

/-- A compatible linear map induces a map of Koszul complexes. -/
def map {N : Type v} [AddCommGroup N] [Module R N]
    (x : M →ₗ[R] R) (y : N →ₗ[R] R) (f : M →ₗ[R] N)
    (hxy : y.comp f = x) :
    complex R M x ⟶ complex R N y :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (exteriorPower.map n f))
    (fun n => by
      rw [complex_d_succ, complex_d_succ]
      apply ModuleCat.hom_ext
      change (differential R N y n).comp (exteriorPower.map (n + 1) f) =
        (exteriorPower.map n f).comp (differential R M x n)
      exact differential_naturality R M x y f hxy n)

/-- A Koszul chain map acts by the exterior-power map in every degree. -/
theorem map_f {N : Type v} [AddCommGroup N] [Module R N]
    (x : M →ₗ[R] R) (y : N →ₗ[R] R) (f : M →ₗ[R] N)
    (hxy : y.comp f = x) (n : ℕ) :
    (map R M x y f hxy).f n =
      ModuleCat.ofHom (exteriorPower.map n f) :=
  rfl

/-- The Koszul map induced by the identity is the identity chain map. -/
theorem map_id (x : M →ₗ[R] R) :
    map R M x x LinearMap.id (by simp) = 𝟙 (complex R M x) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [map_f, HomologicalComplex.id_f, exteriorPower.map_id]
  rfl

/-- Koszul maps respect source-first composition. -/
theorem map_comp
    {N P : Type v} [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (x : M →ₗ[R] R) (y : N →ₗ[R] R) (z : P →ₗ[R] R)
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hxy : y.comp f = x) (hyz : z.comp g = y)
    (hxz : z.comp (g.comp f) = x) :
    map R M x y f hxy ≫ map R N y z g hyz =
      map R M x z (g.comp f) hxz := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, map_f, map_f, map_f]
  apply ModuleCat.hom_ext
  change (exteriorPower.map n g).comp (exteriorPower.map n f) = exteriorPower.map n (g.comp f)
  exact (exteriorPower.map_comp (n := n) f g).symm

/-- A compatible linear equivalence induces an isomorphism of Koszul
complexes over a fixed ring. -/
@[no_expose]
def mapIso {N : Type v} [AddCommGroup N] [Module R N]
    (x : M →ₗ[R] R) (y : N →ₗ[R] R) (e : M ≃ₗ[R] N)
    (hxy : y.comp e.toLinearMap = x) :
    complex R M x ≅ complex R N y := by
  have hyx : x.comp e.symm.toLinearMap = y := by
    rw [← hxy, LinearMap.comp_assoc]
    simp
  exact
    { hom := map R M x y e.toLinearMap hxy
      inv := map R N y x e.symm.toLinearMap hyx
      hom_inv_id := by
        apply HomologicalComplex.hom_ext
        intro n
        rw [HomologicalComplex.comp_f, map_f, map_f,
          HomologicalComplex.id_f]
        apply ModuleCat.hom_ext
        change (exteriorPower.map n e.symm.toLinearMap).comp (exteriorPower.map n e.toLinearMap) =
          LinearMap.id
        rw [← exteriorPower.map_comp]
        simp
      inv_hom_id := by
        apply HomologicalComplex.hom_ext
        intro n
        rw [HomologicalComplex.comp_f, map_f, map_f,
          HomologicalComplex.id_f]
        apply ModuleCat.hom_ext
        change (exteriorPower.map n e.toLinearMap).comp (exteriorPower.map n e.symm.toLinearMap) =
          LinearMap.id
        rw [← exteriorPower.map_comp]
        simp }

/-- The forward map of `mapIso` is the exterior-power map in every degree. -/
theorem mapIso_hom_f {N : Type v} [AddCommGroup N] [Module R N]
    (x : M →ₗ[R] R) (y : N →ₗ[R] R) (e : M ≃ₗ[R] N)
    (hxy : y.comp e.toLinearMap = x) (n : ℕ) :
    (mapIso R M x y e hxy).hom.f n =
      ModuleCat.ofHom (exteriorPower.map n e.toLinearMap) :=
  map_f R M x y e.toLinearMap hxy n

end KoszulComplex

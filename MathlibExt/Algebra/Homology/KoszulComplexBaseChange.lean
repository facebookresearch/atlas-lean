/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.KoszulComplex
public import MathlibExt.LinearAlgebra.ExteriorPower.ContractionBaseChange
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.Additive

/-!
# Base change for Koszul complexes

This file compares the scalar extension of the Koszul complex of a linear
functional with the Koszul complex of its scalar extension. Independent
carrier universes are handled by the canonical `ModuleCat.uliftFunctor` on
the target complex.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace KoszulComplex

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
variable (M : Type w) [AddCommGroup M] [Module R M]

/-- Compatibility facade for Mathlib's scalar extension of a dual vector. -/
def baseChangeFunctional (x : M →ₗ[R] R) : S ⊗[R] M →ₗ[S] S :=
  Module.Dual.baseChange S x

@[simp]
theorem baseChangeFunctional_tmul (x : M →ₗ[R] R) (s : S) (m : M) :
    baseChangeFunctional R S M x (s ⊗ₜ[R] m) =
      algebraMap R S (x m) * s := by
  rw [baseChangeFunctional, Module.Dual.baseChange_apply_tmul,
    Algebra.smul_def]

/-- The scalar extension of a Koszul complex, with scalar-extended terms and
differentials. -/
def baseChangeComplex (x : M →ₗ[R] R) :
    ChainComplex (ModuleCat.{max u v w} S) ℕ :=
  ChainComplex.of
    (fun n => ModuleCat.of S (S ⊗[R] (⋀[R]^n M)))
    (fun n => ModuleCat.ofHom ((differential R M x n).baseChange S))
    (fun n => by
      rw [← ModuleCat.ofHom_comp, ← LinearMap.baseChange_comp,
        differential_comp_differential, LinearMap.baseChange_zero,
        ModuleCat.ofHom_zero])

/-- The degree-`n` object of the scalar-extended Koszul complex. -/
theorem baseChangeComplex_X (x : M →ₗ[R] R) (n : ℕ) :
    (baseChangeComplex R S M x).X n =
      ModuleCat.of S (S ⊗[R] (⋀[R]^n M)) := by
  unfold baseChangeComplex
  rfl

/-- The successor differential of the scalar-extended Koszul complex. -/
theorem baseChangeComplex_d_succ (x : M →ₗ[R] R) (n : ℕ) :
    (baseChangeComplex R S M x).d (n + 1) n =
      ModuleCat.ofHom ((differential R M x n).baseChange S) := by
  unfold baseChangeComplex
  simp [ChainComplex.of_d]

/-- The Koszul differential commutes with scalar extension. -/
theorem differential_baseChange (x : M →ₗ[R] R) (n : ℕ) :
    (differential S (S ⊗[R] M) (baseChangeFunctional R S M x) n).comp
        (exteriorPower.baseChangeMap R S M (n + 1)) =
      (exteriorPower.baseChangeMap R S M n).comp
        ((differential R M x n).baseChange S) := by
  simpa only [differential_eq_contractLeft, baseChangeFunctional] using
    exteriorPower.contractLeft_baseChange R S M x n

/-- The target Koszul complex, universe-lifted into the same `ModuleCat` as
the scalar-extended source. -/
def baseChangeTargetComplex (x : M →ₗ[R] R) :
    ChainComplex (ModuleCat.{max u v w} S) ℕ :=
  ((ModuleCat.uliftFunctor.{u, max v w} S).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
    (complex S (S ⊗[R] M) (baseChangeFunctional R S M x))

/-- The degree-`n` object of the universe-lifted target complex. -/
theorem baseChangeTargetComplex_X (x : M →ₗ[R] R) (n : ℕ) :
    (baseChangeTargetComplex R S M x).X n =
      ModuleCat.of S
        (ULift.{u, max v w} (⋀[S]^n (S ⊗[R] M))) := by
  unfold baseChangeTargetComplex
  rfl

/-- The successor differential of the universe-lifted target complex. -/
theorem baseChangeTargetComplex_d_succ (x : M →ₗ[R] R) (n : ℕ) :
    (baseChangeTargetComplex R S M x).d (n + 1) n =
      ModuleCat.ofHom
        (ULift.moduleEquiv.symm.toLinearMap.comp
          ((differential S (S ⊗[R] M)
            (baseChangeFunctional R S M x) n).comp
              ULift.moduleEquiv.toLinearMap)) := by
  unfold baseChangeTargetComplex
  change (ModuleCat.uliftFunctor.{u, max v w} S).map
      ((complex S (S ⊗[R] M)
        (baseChangeFunctional R S M x)).d (n + 1) n) = _
  rw [complex_d_succ, ModuleCat.uliftFunctor_map]
  rfl

/-- Universe-lifted form of the exterior base-change equivalence. -/
@[no_expose]
def baseChangeLiftedEquiv (n : ℕ) :
    S ⊗[R] (⋀[R]^n M) ≃ₗ[S]
      ULift.{u, max v w} (⋀[S]^n (S ⊗[R] M)) :=
  (exteriorPower.baseChangeEquiv R S M n).trans
    ULift.moduleEquiv.symm

@[simp]
theorem baseChangeLiftedEquiv_apply_tmul_ιMulti
    (n : ℕ) (s : S) (a : Fin n → M) :
    baseChangeLiftedEquiv R S M n
        (s ⊗ₜ[R] exteriorPower.ιMulti R n a) =
      ULift.up (s • exteriorPower.ιMulti S n
        (fun i => (1 : S) ⊗ₜ[R] a i)) := by
  rw [baseChangeLiftedEquiv,
    LinearEquiv.trans_apply,
    exteriorPower.baseChangeEquiv_apply_tmul_ιMulti]
  rfl

private theorem baseChangeLiftedEquiv_down (n : ℕ) :
    ULift.moduleEquiv.toLinearMap.comp
        (baseChangeLiftedEquiv R S M n).toLinearMap =
      exteriorPower.baseChangeMap R S M n := by
  apply TensorProduct.AlgebraTensorModule.curry_injective
  apply LinearMap.ext
  intro s
  apply exteriorPower.linearMap_ext
    (R := R) (n := n) (M := M) (N := ⋀[S]^n (S ⊗[R] M))
  apply AlternatingMap.ext
  intro a
  change (baseChangeLiftedEquiv R S M n
      (s ⊗ₜ[R] exteriorPower.ιMulti R n a)).down =
    exteriorPower.baseChangeMap R S M n
      (s ⊗ₜ[R] exteriorPower.ιMulti R n a)
  rw [baseChangeLiftedEquiv_apply_tmul_ιMulti,
    exteriorPower.baseChangeMap_apply_tmul_ιMulti]

private theorem differential_baseChange_lifted
    (x : M →ₗ[R] R) (n : ℕ) :
    (ULift.moduleEquiv.symm.toLinearMap.comp
        ((differential S (S ⊗[R] M)
          (baseChangeFunctional R S M x) n).comp
            ULift.moduleEquiv.toLinearMap)).comp
      (baseChangeLiftedEquiv R S M (n + 1)).toLinearMap =
    (baseChangeLiftedEquiv R S M n).toLinearMap.comp
      ((differential R M x n).baseChange S) := by
  apply LinearMap.ext
  intro q
  apply ULift.down_injective
  change differential S (S ⊗[R] M)
      (baseChangeFunctional R S M x) n
      (baseChangeLiftedEquiv R S M (n + 1) q).down =
    (baseChangeLiftedEquiv R S M n
      (((differential R M x n).baseChange S) q)).down
  have hnext :
      (baseChangeLiftedEquiv R S M (n + 1) q).down =
        exteriorPower.baseChangeMap R S M (n + 1) q :=
    LinearMap.congr_fun (baseChangeLiftedEquiv_down R S M (n + 1)) q
  have hn :
      (baseChangeLiftedEquiv R S M n
        (((differential R M x n).baseChange S) q)).down =
      exteriorPower.baseChangeMap R S M n
        (((differential R M x n).baseChange S) q) :=
    LinearMap.congr_fun (baseChangeLiftedEquiv_down R S M n)
      (((differential R M x n).baseChange S) q)
  rw [hnext, hn]
  exact LinearMap.congr_fun (differential_baseChange R S M x n) q

/-- The degreewise module isomorphism underlying `baseChangeIso`. -/
@[no_expose]
def baseChangeComponentIso
    (x : M →ₗ[R] R) (n : ℕ) :
    (baseChangeComplex R S M x).X n ≅
      (baseChangeTargetComplex R S M x).X n :=
  eqToIso (baseChangeComplex_X R S M x n) ≪≫
    (baseChangeLiftedEquiv R S M n).toModuleIso ≪≫
      eqToIso (baseChangeTargetComplex_X R S M x n).symm

/-- Scalar extension of a Koszul complex is isomorphic to the
universe-lifted Koszul complex of the scalar-extended functional. -/
@[no_expose]
def baseChangeIso (x : M →ₗ[R] R) :
    baseChangeComplex R S M x ≅ baseChangeTargetComplex R S M x :=
  HomologicalComplex.Hom.isoOfComponents
    (baseChangeComponentIso R S M x)
    (fun i j hij => by
      change j + 1 = i at hij
      subst i
      rw [baseChangeComplex_d_succ, baseChangeTargetComplex_d_succ]
      change ModuleCat.ofHom
          (baseChangeLiftedEquiv R S M (j + 1)).toLinearMap ≫
            ModuleCat.ofHom
              (ULift.moduleEquiv.symm.toLinearMap.comp
                ((differential S (S ⊗[R] M)
                  (baseChangeFunctional R S M x) j).comp
                    ULift.moduleEquiv.toLinearMap)) =
        ModuleCat.ofHom ((differential R M x j).baseChange S) ≫
          ModuleCat.ofHom
            (baseChangeLiftedEquiv R S M j).toLinearMap
      rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
      exact ModuleCat.hom_ext
        (differential_baseChange_lifted R S M x j))

/-- The forward component of `baseChangeIso` is the reviewed degreewise
component isomorphism. -/
theorem baseChangeIso_hom_f
    (x : M →ₗ[R] R) (n : ℕ) :
    (baseChangeIso R S M x).hom.f n =
      (baseChangeComponentIso R S M x n).hom := by
  unfold baseChangeIso
  rfl

/-- The actual chain isomorphism maps a word by the canonical scalar-extension formula. -/
@[simp]
theorem baseChangeIso_hom_f_tmul_ιMulti
    (x : M →ₗ[R] R) (n : ℕ) (s : S) (a : Fin n → M) :
    ((baseChangeIso R S M x).hom.f n).hom (s ⊗ₜ[R] exteriorPower.ιMulti R n a) =
      ULift.up (s • exteriorPower.ιMulti S n
        (fun i => (1 : S) ⊗ₜ[R] a i)) := by
  rw [baseChangeIso_hom_f]
  change baseChangeLiftedEquiv R S M n
    (s ⊗ₜ[R] exteriorPower.ιMulti R n a) = _
  exact baseChangeLiftedEquiv_apply_tmul_ιMulti R S M n s a

end KoszulComplex

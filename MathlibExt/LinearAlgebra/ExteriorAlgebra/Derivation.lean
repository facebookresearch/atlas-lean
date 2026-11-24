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

public import Mathlib.LinearAlgebra.CliffordAlgebra.Fold
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.NoncommRing

/-!
# Exterior derivations induced by linear endomorphisms

A linear endomorphism of a module extends uniquely to an ordinary derivation
of its exterior algebra. The construction uses `CliffordAlgebra.foldr'` with
zero quadratic form, so it applies over every commutative ring and does not
require a basis. It is linear in the endomorphism, preserves exterior degree,
and preserves commutators.

The ambient exterior algebra is generally noncommutative. The derivations
are represented by linear endomorphisms with their proved Leibniz equation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

private def derivationStep (g : Module.End R M) :
    M →ₗ[R] (ExteriorAlgebra R M × ExteriorAlgebra R M) →ₗ[R]
      ExteriorAlgebra R M :=
  (((Algebra.lmul R (ExteriorAlgebra R M)).toLinearMap.comp
      ((ι R).comp g)).compl₂
    (LinearMap.fst R (ExteriorAlgebra R M) (ExteriorAlgebra R M))) +
  (((Algebra.lmul R (ExteriorAlgebra R M)).toLinearMap.comp
      (ι R)).compl₂
    (LinearMap.snd R (ExteriorAlgebra R M) (ExteriorAlgebra R M)))

private lemma derivationStep_apply (g : Module.End R M) (x : M)
    (a : ExteriorAlgebra R M × ExteriorAlgebra R M) :
    derivationStep R M g x a = ι R (g x) * a.1 + ι R x * a.2 :=
  rfl

private theorem derivationStep_relation (g : Module.End R M)
    (x : M) (a b : ExteriorAlgebra R M) :
    derivationStep R M g x
        (ι R x * a, derivationStep R M g x (a, b)) =
      (0 : QuadraticForm R M) x • b := by
  have hanti : ι R (g x) * ι R x + ι R x * ι R (g x) = 0 :=
    ι_add_mul_swap (g x) x
  have hz : (0 : QuadraticForm R M) x • b = (0 : ExteriorAlgebra R M) := by
    simp
  rw [hz]
  change ι R (g x) * (ι R x * a) +
    ι R x * (ι R (g x) * a + ι R x * b) = 0
  calc
    _ = (ι R (g x) * ι R x + ι R x * ι R (g x)) * a +
        (ι R x * ι R x) * b := by noncomm_ring
    _ = 0 := by rw [hanti, ι_sq_zero, zero_mul, zero_mul, add_zero]

private def derivationAux (g : Module.End R M) :
    Module.End R (ExteriorAlgebra R M) :=
  CliffordAlgebra.foldr' (0 : QuadraticForm R M)
    (derivationStep R M g) (derivationStep_relation R M g) 0

private theorem derivationAux_algebraMap (g : Module.End R M) (r : R) :
    derivationAux R M g (algebraMap R (ExteriorAlgebra R M) r) = 0 := by
  simp [derivationAux, CliffordAlgebra.foldr'_algebraMap]

private theorem derivationAux_ι_mul (g : Module.End R M) (x : M)
    (a : ExteriorAlgebra R M) :
    derivationAux R M g (ι R x * a) =
      ι R (g x) * a + ι R x * derivationAux R M g a := by
  simpa only [derivationAux, derivationStep_apply] using
    (CliffordAlgebra.foldr'_ι_mul (0 : QuadraticForm R M)
      (derivationStep R M g) (derivationStep_relation R M g)
      (0 : ExteriorAlgebra R M) x a)

private theorem derivationAux_add (g h : Module.End R M) :
    derivationAux R M (g + h) = derivationAux R M g + derivationAux R M h := by
  apply LinearMap.ext
  intro a
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp only [LinearMap.add_apply, derivationAux_algebraMap, add_zero]
  | add a b ha hb =>
      simp only [LinearMap.add_apply, map_add, ha, hb]
  | ι_mul a x ha =>
      simp only [LinearMap.add_apply, derivationAux_ι_mul, map_add,
        ha, add_mul, mul_add]; abel

private theorem derivationAux_smul (r : R) (g : Module.End R M) :
    derivationAux R M (r • g) = r • derivationAux R M g := by
  apply LinearMap.ext
  intro a
  induction a using CliffordAlgebra.left_induction with
  | algebraMap t =>
      simp only [LinearMap.smul_apply, derivationAux_algebraMap, smul_zero]
  | add a b ha hb =>
      simp only [LinearMap.smul_apply, map_add, ha, hb]
  | ι_mul a x ha =>
      simp only [LinearMap.smul_apply, derivationAux_ι_mul, map_smul,
        ha, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_add]

/-- Extend a linear endomorphism to the derivation that acts on each
exterior generator by that endomorphism. -/
def derivation : Module.End R M →ₗ[R] Module.End R (ExteriorAlgebra R M) where
  toFun := private derivationAux R M
  map_add' := by exact derivationAux_add R M
  map_smul' := by exact derivationAux_smul R M

/-- The induced derivation vanishes on scalars. -/
@[simp]
theorem derivation_algebraMap (g : Module.End R M) (r : R) :
    derivation R M g (algebraMap R (ExteriorAlgebra R M) r) = 0 :=
  derivationAux_algebraMap R M g r

/-- The induced derivation vanishes on the multiplicative identity. -/
@[simp]
theorem derivation_one (g : Module.End R M) :
    derivation R M g 1 = 0 := by
  simpa only [map_one] using derivation_algebraMap R M g 1

/-- The generator recursion for the induced exterior derivation. -/
@[simp]
theorem derivation_ι_mul (g : Module.End R M) (x : M)
    (a : ExteriorAlgebra R M) :
    derivation R M g (ι R x * a) =
      ι R (g x) * a + ι R x * derivation R M g a :=
  derivationAux_ι_mul R M g x a

/-- The induced derivation agrees with the supplied endomorphism on
exterior generators. -/
@[simp]
theorem derivation_ι (g : Module.End R M) (x : M) :
    derivation R M g (ι R x) = ι R (g x) := by
  simpa only [mul_one, derivation_one, mul_zero, add_zero] using
    derivation_ι_mul R M g x 1

/-- The ordinary Leibniz equation in the exterior algebra. -/
theorem derivation_mul (g : Module.End R M) (a b : ExteriorAlgebra R M) :
    derivation R M g (a * b) =
      derivation R M g a * b + a * derivation R M g b := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp only [← Algebra.smul_def, map_smul, derivation_algebraMap,
        zero_mul, zero_add]
  | add a a' ha ha' =>
      simp only [add_mul, map_add, ha, ha']; abel
  | ι_mul a x ha =>
      rw [mul_assoc, derivation_ι_mul, ha, derivation_ι_mul]
      noncomm_ring

/-- A derivation of the exterior algebra is determined by its action on
scalars and its generator recursion. -/
theorem derivation_unique (g : Module.End R M)
    (D : Module.End R (ExteriorAlgebra R M))
    (hR : ∀ r : R, D (algebraMap R (ExteriorAlgebra R M) r) = 0)
    (hι : ∀ (x : M) (a : ExteriorAlgebra R M),
      D (ι R x * a) = ι R (g x) * a + ι R x * D a) :
    D = derivation R M g := by
  apply LinearMap.ext
  intro a
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r => rw [hR, derivation_algebraMap]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | ι_mul a x ha => rw [hι, derivation_ι_mul, ha]

/-- The induced derivation preserves each homogeneous exterior degree. -/
theorem derivation_mem_exteriorPower (g : Module.End R M) (n : ℕ)
    (a : ExteriorAlgebra R M) (ha : a ∈ ⋀[R]^n M) :
    derivation R M g a ∈ ⋀[R]^n M := by
  dsimp only [ExteriorAlgebra.exteriorPower] at ha ⊢
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r =>
      rw [derivation_algebraMap]
      exact Submodule.zero_mem _
  | add a b n ha hb iha ihb =>
      rw [map_add]
      exact Submodule.add_mem _ iha ihb
  | mem_mul m hm n a ha ih =>
      obtain ⟨x, rfl⟩ := hm
      rw [derivation_ι_mul, pow_succ']
      exact Submodule.add_mem _
        (Submodule.mul_mem_mul (LinearMap.mem_range_self _ (g x)) ha)
        (Submodule.mul_mem_mul (LinearMap.mem_range_self _ x) ih)

/-- Extending endomorphisms to exterior derivations preserves their
commutator. -/
theorem derivation_commutator (g h : Module.End R M) :
    derivation R M (g.comp h - h.comp g) =
      (derivation R M g).comp (derivation R M h) -
        (derivation R M h).comp (derivation R M g) := by
  apply LinearMap.ext
  intro a
  change derivation R M (g.comp h - h.comp g) a =
    derivation R M g (derivation R M h a) -
      derivation R M h (derivation R M g a)
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r => simp only [derivation_algebraMap, map_zero, sub_self]
  | add a b ha hb => simp only [map_add, ha, hb]; noncomm_ring
  | ι_mul a x ha =>
      rw [derivation_ι_mul, ha]
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
        derivation_ι_mul, map_add]; noncomm_ring

/-- Exterior derivations are natural for linear maps intertwining the
endomorphisms on the two modules. -/
theorem derivation_naturality
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (g : Module.End R M) (h : Module.End R N)
    (hfg : f.comp g = h.comp f) :
    (ExteriorAlgebra.map f).toLinearMap.comp (derivation R M g) =
      (derivation R N h).comp (ExteriorAlgebra.map f).toLinearMap := by
  have hinter (x : M) : f (g x) = h (f x) := LinearMap.congr_fun hfg x
  apply LinearMap.ext
  intro a
  change ExteriorAlgebra.map f (derivation R M g a) =
    derivation R N h (ExteriorAlgebra.map f a)
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      rw [derivation_algebraMap, map_zero, AlgHom.commutes, derivation_algebraMap]
  | add a b ha hb => simp only [map_add, ha, hb]
  | ι_mul a x ha =>
      simp only [derivation_ι_mul, map_mul, map_add,
        ExteriorAlgebra.map_apply_ι, hinter, ha]

section Lie

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The extension to exterior derivations, bundled as a Lie homomorphism
between the native commutator Lie algebras of endomorphisms. -/
def derivationLieHom :
    Module.End R M →ₗ⁅R⁆ Module.End R (ExteriorAlgebra R M) where
  __ := derivation R M
  map_lie' {g h} := by
    change derivation R M (g * h - h * g) =
      derivation R M g * derivation R M h -
        derivation R M h * derivation R M g
    simpa only [Module.End.mul_eq_comp] using derivation_commutator R M g h

/-- Forgetting the commutator compatibility recovers the same linear
extension to exterior derivations. -/
@[simp]
theorem derivationLieHom_toLinearMap :
    (derivationLieHom R M).toLinearMap = derivation R M :=
  rfl

end Lie

end ExteriorAlgebra

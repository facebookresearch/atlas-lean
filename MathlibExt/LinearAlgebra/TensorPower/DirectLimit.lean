/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Avocado
-/
module

public import Mathlib.LinearAlgebra.TensorPower.Basic
public import MathlibExt.LinearAlgebra.TensorProduct.DirectLimit.Finite

/-!
# Positive native tensor powers and directed limits

Over a commutative semiring, the native tensor power with `n + 1` factors commutes with a
module direct limit indexed by a directed preorder. Its transitions apply the original
linear map in each factor. Scalar, stage and carrier universes are independent. No nonempty
index, injectivity, flatness or additive-inverse assumption is required.

The comparison uses the finite-family tensor comparison and the native ordered last-factor
splitting. It does not introduce another tensor-power carrier or recursive map encoding.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped TensorProduct
open Module Module.DirectLimit

universe u v w

namespace TensorPower

variable {R : Type u} [CommSemiring R] {ι : Type v} [Preorder ι] [DecidableEq ι]
  {G : ι → Type w} [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
  (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

/-- The transition on the native positive tensor power acts in every factor. -/
def directedTransition (n : ℕ) (i j : ι) (h : i ≤ j) :
    TensorPower R (n + 1) (G i) →ₗ[R] TensorPower R (n + 1) (G j) :=
  PiTensorProduct.map (fun _ : Fin (n + 1) => f i j h)

variable [DirectedSystem G (f · · ·)]

instance directedSystem (n : ℕ) :
    DirectedSystem (fun i => TensorPower R (n + 1) (G i)) (directedTransition f n · · ·) where
  map_self {i} x := by
    have h : (fun _ : Fin (n + 1) => f i i le_rfl) =
        (fun _ => (LinearMap.id : G i →ₗ[R] G i)) := by
      funext j
      apply LinearMap.ext
      intro z
      exact DirectedSystem.map_self' f z
    rw [directedTransition, h, PiTensorProduct.map_id]
    rfl
  map_map {k j i} hij hjk x := by
    have h : (fun _ : Fin (n + 1) => (f j k hjk).comp (f i j hij)) =
        (fun _ => f i k (hij.trans hjk)) := by
      funext a
      apply LinearMap.ext
      intro z
      exact DirectedSystem.map_map' f hij hjk z
    rw [directedTransition, directedTransition, ← LinearMap.comp_apply,
      ← PiTensorProduct.map_comp, h]
    rfl

/-- Put the last factor first while retaining the ordered native prefix. -/
def lastFactorFirst (M : Type w) [AddCommMonoid M] [Module R M] (n : ℕ) :
    TensorPower R (n + 1) M ≃ₗ[R] M ⊗[R] TensorPower R n M :=
  PiTensorProduct.finSnocEquiv R n (fun _ => M) ≪≫ₗ
    TensorProduct.comm R (TensorPower R n M) M

@[simp]
theorem lastFactorFirst_tprod (M : Type w) [AddCommMonoid M] [Module R M]
    (n : ℕ) (x : Fin (n + 1) → M) :
    lastFactorFirst (R := R) M n (PiTensorProduct.tprod R x) =
      x (Fin.last n) ⊗ₜ[R] PiTensorProduct.tprod R (fun j : Fin n => x j.castSucc) := by
  simp [lastFactorFirst]

omit [DirectedSystem G (f · · ·)] in
/-- The last-factor splitting commutes with simultaneous transition maps. -/
theorem lastFactorFirst_transition (n : ℕ) (i j : ι) (hij : i ≤ j) :
    (lastFactorFirst (R := R) (G j) n).toLinearMap.comp (directedTransition f n i j hij) =
      (TensorProduct.finiteDiagonalTransition f (fun _ : Fin n => f) i j hij).comp
        (lastFactorFirst (R := R) (G i) n).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    directedTransition, PiTensorProduct.map_tprod, lastFactorFirst_tprod,
    TensorProduct.finiteDiagonalTransition, TensorProduct.map_tmul]

variable [IsDirectedOrder ι]

/-- Native positive tensor powers commute with a directed module limit. -/
def directLimit (n : ℕ) :
    TensorPower R (n + 1) (Module.DirectLimit G f) ≃ₗ[R]
      Module.DirectLimit (fun i => TensorPower R (n + 1) (G i)) (directedTransition f n) :=
  lastFactorFirst (R := R) (Module.DirectLimit G f) n ≪≫ₗ
    TensorProduct.directLimitFinite f (fun _ : Fin n => f) ≪≫ₗ
      (Module.DirectLimit.congr
        (fun i => lastFactorFirst (R := R) (G i) n)
        (lastFactorFirst_transition f n)).symm

/-- The inverse comparison preserves every pure tensor represented at one stage. -/
@[simp]
theorem directLimit_symm_of_tprod (n : ℕ) (i : ι) (x : Fin (n + 1) → G i) :
    (directLimit f n).symm
        (Module.DirectLimit.of R ι (fun j => TensorPower R (n + 1) (G j))
          (directedTransition f n) i (PiTensorProduct.tprod R x)) =
      PiTensorProduct.tprod R (fun a => Module.DirectLimit.of R ι G f i (x a)) := by
  apply (lastFactorFirst (R := R) (Module.DirectLimit G f) n).injective
  simp only [directLimit, LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, Module.DirectLimit.congr_apply_of, lastFactorFirst_tprod,
    TensorProduct.directLimitFinite_symm_of_tprod]

/-- The comparison sends a pure tensor of same-stage classes to its stage tensor. -/
@[simp]
theorem directLimit_tprod_of (n : ℕ) (i : ι) (x : Fin (n + 1) → G i) :
    directLimit f n (PiTensorProduct.tprod R (fun a => Module.DirectLimit.of R ι G f i (x a))) =
      Module.DirectLimit.of R ι (fun j => TensorPower R (n + 1) (G j))
        (directedTransition f n) i (PiTensorProduct.tprod R x) := by
  rw [← directLimit_symm_of_tprod f n i x, LinearEquiv.apply_symm_apply]

/-- A native positive-power tensor vanishing in the limit is killed at a later stage. -/
theorem exists_eq_zero_of_map_to_directLimit_eq_zero (n : ℕ) {i : ι}
    (x : TensorPower R (n + 1) (G i))
    (hx : PiTensorProduct.map (fun _ : Fin (n + 1) => Module.DirectLimit.of R ι G f i) x = 0) :
    ∃ j : ι, ∃ hij : i ≤ j, directedTransition f n i j hij x = 0 := by
  have hmap : (directLimit f n).symm.toLinearMap.comp
      (Module.DirectLimit.of R ι (fun j => TensorPower R (n + 1) (G j))
        (directedTransition f n) i) =
      PiTensorProduct.map (fun _ : Fin (n + 1) => Module.DirectLimit.of R ι G f i) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro y
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      directLimit_symm_of_tprod, PiTensorProduct.map_tprod]
  have hz : Module.DirectLimit.of R ι (fun j => TensorPower R (n + 1) (G j))
      (directedTransition f n) i x = 0 := by
    apply (directLimit f n).symm.injective
    rw [← LinearMap.comp_apply, hmap, hx, map_zero]
  exact Module.DirectLimit.of.zero_exact hz

end TensorPower

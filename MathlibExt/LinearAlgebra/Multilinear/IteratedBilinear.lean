/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import Mathlib.LinearAlgebra.Multilinear.Curry

/-! # Ordered multilinear iteration and adjacent vanishing of bilinear steps -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
universe r a b
namespace TopModuleCat
variable {R : Type r} [CommRing R] [TopologicalSpace R]

/-- Postcomposition through a genuine scalar-module isomorphism. -/
def bilinearThroughModuleIso {M N P Q : TopModuleCat.{b} R}
    (e : P ≅ Q) (f : M →ₗ[R] N →ₗ[R] P) : M →ₗ[R] N →ₗ[R] Q :=
  f.compr₂ e.hom.hom.toLinearMap

/-- Bilinear maps retain the stored scalar modules and the stock
scalar action on the inner linear-map object. -/
abbrev storedBilinearMap.{rr,bb} {S : Type rr} [CommRing S] [TopologicalSpace S]
    (X Y Z : TopModuleCat.{bb} S) :=
  X →ₗ[S] Y →ₗ[S] Z

end TopModuleCat

namespace MultilinearMap
variable {R : Type r} [CommRing R] [TopologicalSpace R]

/-- Ordered multilinear iteration of the actual supplied bilinear steps and zero-degree vector. -/
def iterateCupMultilinear (V : Type a) [AddCommGroup V] [Module R V]
    (A : TopModuleCat.{b} R) (C : ℕ → TopModuleCat.{b} R)
    (kappa : V →ₗ[R] A) (unit : C 0)
    (step : (n : ℕ) → A →ₗ[R] C n →ₗ[R] C (n + 1)) :
    (n : ℕ) → MultilinearMap R (fun _ : Fin n => V) (C n)
  | 0 => MultilinearMap.constOfIsEmpty R _ unit
  | n + 1 =>
    let B := iterateCupMultilinear V A C kappa unit step n
    let f : V →ₗ[R] MultilinearMap R (fun _ : Fin n => V) (C (n + 1)) :=
      { toFun := fun x => ((step n) (kappa x)).compMultilinearMap B
        map_add' := fun x y => by
          apply MultilinearMap.ext
          intro v
          change step n (kappa (x + y)) (B v) = step n (kappa x) (B v) + step n (kappa y) (B v)
          rw [map_add, map_add, LinearMap.add_apply]
        map_smul' := fun s x => by
          apply MultilinearMap.ext
          intro v
          change step n (kappa (s • x)) (B v) = s • step n (kappa x) (B v)
          rw [map_smul, map_smul, LinearMap.smul_apply] }
    f.uncurryLeft

/-- The multilinear iteration has the literal ordered head and tail formula. -/
theorem iterateCupMultilinear_succ (V : Type a) [AddCommGroup V] [Module R V]
    (A : TopModuleCat.{b} R) (C : ℕ → TopModuleCat.{b} R)
    (kappa : V →ₗ[R] A) (unit : C 0)
    (step : (n : ℕ) → A →ₗ[R] C n →ₗ[R] C (n + 1))
    (n : ℕ) (v : Fin (n + 1) → V) :
    iterateCupMultilinear V A C kappa unit step (n + 1) v =
      step n (kappa (v 0)) (iterateCupMultilinear V A C kappa unit step n (fun i => v i.succ)) := rfl

/-- A vanishing adjacent pair of true bilinear steps kills every insertion in the ordered iteration. -/
theorem iterateCupMultilinear_adjacent {R : Type r} [CommRing R] [TopologicalSpace R]
    (V : Type a) [AddCommGroup V] [Module R V]
    (A : TopModuleCat.{b} R) (C : ℕ → TopModuleCat.{b} R)
    (kappa : V →ₗ[R] A) (unit : C 0)
    (step : (n : ℕ) → A →ₗ[R] C n →ₗ[R] C (n + 1))
    (P : V → V → Prop)
    (hpair : ∀ (n : ℕ) (x y : V), P x y → ∀ z : C n,
      step (n + 1) (kappa x) (step n (kappa y) z) = 0) :
    ∀ (n : ℕ) (v : Fin n → V) (i : Fin n) (hi : i.val + 1 < n),
      P (v i) (v ⟨i.val + 1, hi⟩) →
        iterateCupMultilinear (R := R) V A C kappa unit step n v = 0 := by
  intro n
  induction n with
  | zero => intro _ i; exact Fin.elim0 i
  | succ n ih =>
    intro v i hi hp
    by_cases hi0 : i.val = 0
    · cases n with
      | zero => omega
      | succ n =>
        have he0 : i = (0 : Fin (n + 2)) := Fin.ext hi0
        have he1 : (⟨i.val + 1, hi⟩ : Fin (n + 2)) = (0 : Fin (n + 1)).succ := by
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_zero, hi0]
        have hp' : P (v 0) (v (0 : Fin (n + 1)).succ) := by
          exact (congrArg₂ P (congrArg v he0) (congrArg v he1)).mp hp
        rw [iterateCupMultilinear_succ, iterateCupMultilinear_succ]
        exact hpair n (v 0) (v (0 : Fin (n + 1)).succ) hp' _
    · let j : Fin n := ⟨i.val - 1, by omega⟩
      let tail : Fin n → V := fun t => v t.succ
      have hj : j.val + 1 < n := by dsimp [j]; omega
      have he0 : tail j = v i := by
        apply congrArg v
        apply Fin.ext
        dsimp [tail, j]
        omega
      have he1 : tail ⟨j.val + 1, hj⟩ = v ⟨i.val + 1, hi⟩ := by
        apply congrArg v
        apply Fin.ext
        dsimp [tail, j]
        omega
      have ht := ih tail j hj (by simpa only [he0, he1] using hp)
      rw [iterateCupMultilinear_succ]
      change step n (kappa (v 0))
        (iterateCupMultilinear (R := R) V A C kappa unit step n tail) = 0
      rw [ht, _root_.map_zero]

end MultilinearMap

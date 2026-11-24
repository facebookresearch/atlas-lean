/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatFiber
public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsMonomialStabilization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.SpecialLinearStabilization
import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatMiddleStabilization

/-!
# Stabilization of the Tits Bruhat fibre

Constructs the successor map on the Tits Bruhat fibre from matrix and monomial
stabilization. It is injective, has explicit formulas on both coordinates and is
natural under field homomorphisms.
-/

@[expose] public section

universe u v

open MatsumotoTitsMonomialExtension
open Matrix.GeneralLinearGroup

namespace MatsumotoTitsBruhatFiber

variable (F : Type u) [Field F] (n : ℕ)

/-- Successor map on the Tits Bruhat pullback fiber.

Uses the accepted component successors `Matrix.SpecialLinearGroup.stabilization`
and `HMTitsSuccHom` and the accepted Bruhat-middle successor theorem
`bruhatMiddle_stabilization`. -/
noncomputable def XSucc (F : Type u) [Field F] (n : ℕ) : X F n → X F (n + 1) :=
  fun x =>
    ⟨(Matrix.SpecialLinearGroup.stabilization F x.val.1,
      HMTitsSuccHom F n x.val.2), by
      have hx : bruhatMiddle x.val.1 = projHom F n x.val.2 := x.2
      calc bruhatMiddle (Matrix.SpecialLinearGroup.stabilization F x.val.1)
          = monomialSLSuccHom (R := F) (bruhatMiddle x.val.1) :=
            bruhatMiddle_stabilization _
        _ = monomialSLSuccHom (R := F) (projHom F n x.val.2) := by
            rw [hx]
        _ = projHom F (n + 1) (HMTitsSuccHom F n x.val.2) := by
            rw [HMTitsSuccHom_proj]⟩

@[simp]
theorem XSucc_fst (F : Type u) [Field F] (n : ℕ) (x : X F n) :
    X.fst (XSucc F n x) = Matrix.SpecialLinearGroup.stabilization F (X.fst x) :=
  rfl

@[simp]
theorem XSucc_snd (F : Type u) [Field F] (n : ℕ) (x : X F n) :
    X.snd (XSucc F n x) = HMTitsSuccHom F n (X.snd x) :=
  rfl

theorem XSucc_wellDefined (F : Type u) [Field F] (n : ℕ) (x : X F n) :
    bruhatMiddle (Matrix.SpecialLinearGroup.stabilization F x.val.1) =
      projHom F (n + 1) (HMTitsSuccHom F n x.val.2) :=
  (XSucc F n x).2

theorem XSucc_injective (F : Type u) [Field F] (n : ℕ) :
    Function.Injective (XSucc F n) := by
  intro x y h
  have hfst :
      Matrix.SpecialLinearGroup.stabilization F (X.fst x) =
        Matrix.SpecialLinearGroup.stabilization F (X.fst y) := by
    have hx := congrArg X.fst h
    simp only [XSucc_fst] at hx
    exact hx
  have hsnd :
      HMTitsSuccHom F n (X.snd x) = HMTitsSuccHom F n (X.snd y) := by
    have hx := congrArg X.snd h
    simp only [XSucc_snd] at hx
    exact hx
  have hx_fst : X.fst x = X.fst y :=
    Matrix.SpecialLinearGroup.stabilization_injective hfst
  have hx_snd : X.snd x = X.snd y :=
    HMTitsSuccHom_injective F n hsnd
  exact X.ext hx_fst hx_snd

variable {F : Type u} [Field F] {K : Type v} [Field K]

theorem XSucc_naturality (f : F →+* K) (n : ℕ) (x : X F n) :
    XMap f (XSucc F n x) = XSucc K n (XMap f x) := by
  apply X.ext
  · simp only [XMap, XSucc]
    rw [← Matrix.SpecialLinearGroup.stabilization_map_apply]
  · simp only [XMap, XSucc]
    have hNat := HMTitsSuccHom_naturality (F := F) (K := K) f n
    exact DFunLike.congr_fun hNat x.val.2

end MatsumotoTitsBruhatFiber

end

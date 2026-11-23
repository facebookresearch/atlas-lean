/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The opposed-bigrading definitions adapt TauCetiProject/TauCeti
62bbc0596dc3539d488232e4e924a338548ea0a9,
TauCeti/Geometry/Hodge/Mixed/Basic.lean and Mixed/Bigrading.lean,
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Authors: The Tau Ceti contributors. Apache License 2.0.
Modification: use the actual native tensor complexification for a subfield
of the reals and retain normalized conjugation and both actual filtrations.
-/
module

public import MathlibExt.Algebra.RealSubfieldCoefficients
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import MathlibExt.Geometry.RationalHodgeStructures
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Real-coefficient Hodge and relative monodromy data

The complex carrier is the native scalar extension of an actual A-module,
where A is a specified subfield of R. Conjugation is fixed on every pure
tensor. Pure and mixed Hodge conditions recover the actual Hodge and weight
filtrations. Relative monodromy uses actual intersection quotients and the
literal powers of the nilpotent operator, including the prescribed centers.

Sources: Morihiko Saito, arXiv:1307.2140v5, sections 1.1 and 2.2;
Deligne, Théorie de Hodge II; the Tau Ceti pointwise definitions above.
These are the concrete fibre/limit data used by variation and V-cycle tests.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.Geometry.RealCoefficientHodgeStructures

open _root_.CategoryTheory
open MathlibExt.Algebra.RealSubfieldCoefficients
open scoped ChangeOfRings

variable (A : Subfield ℝ) (V : ModuleCat.{0} A)

abbrev complexCarrier := (ModuleCat.extendScalars (complexEmbedding A)).obj V

def tensorValue (z : ℂ) (v : V) : complexCarrier A V := z ⊗ₜ[A, complexEmbedding A] v

structure Conjugation where
  map : complexCarrier A V ≃ₛₗ[starRingEnd ℂ] complexCarrier A V
  involutive : Function.Involutive map
  tensor_normalization : ∀ z v, map (tensorValue A V z v) = tensorValue A V (star z) v

def complexifiedSubspace (P : Submodule A V) : Submodule ℂ (complexCarrier A V) :=
  Submodule.span ℂ (tensorValue A V 1 '' (P : Set V))

structure PureHodgeStructure (C : Conjugation A V) (w : ℤ) where
  [finite : FiniteDimensional A V]
  F : ℤ → Submodule ℂ (complexCarrier A V)
  antitone : Antitone F
  exhaustive : ∃ p, F p = ⊤
  bounded : ∃ p, F p = ⊥
  opposed : ∀ p, IsCompl (F p) ((F (w + 1 - p)).map C.map.toLinearMap)

structure HodgeBigrading (C : Conjugation A V) (W : ℤ → Submodule A V)
    (F : ℤ → Submodule ℂ (complexCarrier A V))
    (I : ℤ × ℤ → Submodule ℂ (complexCarrier A V)) : Prop where
  independent : iSupIndep I
  weights : ∀ k, complexifiedSubspace A V (W k) =
    ⨆ (pq : ℤ × ℤ) (_ : pq.1 + pq.2 ≤ k), I pq
  hodge : ∀ p, F p = ⨆ (pq : ℤ × ℤ) (_ : p ≤ pq.1), I pq
  conjugate_lower : ∀ pq, (I pq).map C.map.toLinearMap ≤
    I pq.swap ⊔ complexifiedSubspace A V (W (pq.1 + pq.2 - 1))

structure MixedHodgeStructure (C : Conjugation A V) where
  [finite : FiniteDimensional A V]
  W : ℤ → Submodule A V
  monotone : Monotone W
  W_top : ∃ k, W k = ⊤
  W_bot : ∃ k, W k = ⊥
  F : ℤ → Submodule ℂ (complexCarrier A V)
  antitone : Antitone F
  F_top : ∃ p, F p = ⊤
  F_bot : ∃ p, F p = ⊥
  bigrading : ∃ I, HodgeBigrading A V C W F I

/-- The pairing is untwisted and A-valued. Its Tate-valued version is the
displayed complex pairing multiplied by (2pi i)^(-w). The sign and Weil
operator below use the Deligne convention on the untwisted pairing. -/
structure PurePolarization (C : Conjugation A V) (w : ℤ) (H : PureHodgeStructure A V C w) where
  form : V →ₗ[A] V →ₗ[A] A
  complexForm : complexCarrier A V →ₗ[ℂ] complexCarrier A V →ₗ[ℂ] ℂ
  coefficient_normalization : ∀ (a b : ℂ) (v t : V),
    complexForm (tensorValue A V a v) (tensorValue A V b t) = a * b * complexEmbedding A (form v t)
  perfect : Function.Bijective form
  parity : ∀ v t, form v t = (-1 : A) ^ w * form t v
  orthogonal : ∀ p v t, v ∈ H.F p → t ∈ H.F (w + 1 - p) → complexForm v t = 0
  hodgeRiemann : ∀ (p q : ℤ), p + q = w → ∀ v : complexCarrier A V,
    v ∈ H.F p ⊓ (H.F q).map C.map.toLinearMap → v ≠ 0 →
      (Complex.I ^ (p - q) * (-1 : ℂ) ^ (w * (w - 1) / 2) * complexForm v (C.map v)).im = 0 ∧
      0 < (Complex.I ^ (p - q) * (-1 : ℂ) ^ (w * (w - 1) / 2) * complexForm v (C.map v)).re

def PurePolarization.tateForm {C : Conjugation A V} {w : ℤ} {H : PureHodgeStructure A V C w}
    (P : PurePolarization A V C w H) :
    complexCarrier A V →ₗ[ℂ] complexCarrier A V →ₗ[ℂ] ℂ :=
  ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) ^ (-w) • P.complexForm

theorem PurePolarization.tateForm_tensor {C : Conjugation A V} {w : ℤ}
    {H : PureHodgeStructure A V C w} (P : PurePolarization A V C w H)
    (a b : ℂ) (v t : V) :
    PurePolarization.tateForm A V P (tensorValue A V a v) (tensorValue A V b t) =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) ^ (-w) *
        (a * b * complexEmbedding A (P.form v t)) := by
  change _ * P.complexForm (tensorValue A V a v) (tensorValue A V b t) = _
  rw [P.coefficient_normalization]

def doubleLower (M W : ℤ → Submodule A V) (i k : ℤ) : Submodule A V :=
  (M (i - 1) ⊓ W k) ⊔ (M i ⊓ W (k - 1))

def doubleUpper (M W : ℤ → Submodule A V) (i k : ℤ) : Submodule A V := M i ⊓ W k

theorem doubleLower_le_doubleUpper (M W : ℤ → Submodule A V)
    (hM : Monotone M) (hW : Monotone W) (i k : ℤ) :
    doubleLower A V M W i k ≤ doubleUpper A V M W i k := by
  apply sup_le
  · exact inf_le_inf (hM (by omega)) le_rfl
  · exact inf_le_inf le_rfl (hW (by omega))

abbrev DoubleGraded (M W : ℤ → Submodule A V) (i k : ℤ) :=
  (↥(doubleUpper A V M W i k)) ⧸
    (doubleLower A V M W i k).comap (doubleUpper A V M W i k).subtype

def doubleClass (M W : ℤ → Submodule A V) (i k : ℤ) (v : V) (hv : v ∈ M i ⊓ W k) :
    DoubleGraded A V M W i k := Submodule.Quotient.mk ⟨v, hv⟩

structure RelativeMonodromyFiltration (W : ℤ → Submodule A V) (N : Module.End A V) where
  weight_monotone : Monotone W
  weight_top : ∃ k, W k = ⊤
  weight_bot : ∃ k, W k = ⊥
  nilpotent : ∃ b : ℕ, N ^ b = 0
  preserveW : ∀ k, (W k).map N ≤ W k
  M : ℤ → Submodule A V
  monotone : Monotone M
  M_top : ∃ i, M i = ⊤
  M_bot : ∃ i, M i = ⊥
  lower_two : ∀ i, (M i).map N ≤ M (i - 2)
  iterate_mem : ∀ (k : ℤ) (j : ℕ) (v : V), v ∈ M (k + j) ⊓ W k →
    N^[j] v ∈ M (k - j) ⊓ W k
  centered_iso : ∀ (k : ℤ) (j : ℕ),
    DoubleGraded A V M W (k + j) k ≃ₗ[A] DoubleGraded A V M W (k - j) k
  operator_normalization : ∀ (k : ℤ) (j : ℕ) (v : V) (hv : v ∈ M (k + j) ⊓ W k),
    centered_iso k j (doubleClass A V M W (k + j) k v hv) =
      doubleClass A V M W (k - j) k (N^[j] v) (iterate_mem k j v hv)

end MathlibExt.Geometry.RealCoefficientHodgeStructures

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_QuaternionAlgebra_ClassSetHecke.lean`,
`Definitions/Def_QuaternionAlgebra_Order_FiniteIdele.lean`,
`Definitions/Def_QuaternionAlgebra_Order.lean` and
`Definitions/Def_QuaternionAlgebra_ReducedNorm.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Quaternion
public import Mathlib.GroupTheory.DoubleCoset
public import MathlibExt.Algebra.Quaternion.FiniteAdeleBox

@[expose] public section

open scoped TensorProduct Pointwise Quaternion
open IsDedekindDomain NumberField

noncomputable section

namespace QuaternionAlgebra

variable {a b : ℚ}

structure IsOrder (Λ : Submodule ℤ ℍ[ℚ, a, b]) : Prop where

  one_mem : (1 : ℍ[ℚ, a, b]) ∈ Λ

  mul_mem : ∀ ⦃x y : ℍ[ℚ, a, b]⦄, x ∈ Λ → y ∈ Λ → x * y ∈ Λ

  spanTop : Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) = ⊤

  fg : Λ.FG

def IsUnitOf (Λ : Submodule ℤ ℍ[ℚ, a, b]) (u : ℍ[ℚ, a, b]) : Prop :=
  u ∈ Λ ∧ ∃ v ∈ Λ, u * v = 1 ∧ v * u = 1

def IsQuadraticDatum (t n : ℤ) (α : ℍ[ℚ, a, b]) : Prop :=
  α * α - (t : ℚ) • α + (n : ℚ) • (1 : ℍ[ℚ, a, b]) = 0

def EmbeddingDatum (Λ : Submodule ℤ ℍ[ℚ, a, b]) (t n : ℤ) : Type :=
  {α : ℍ[ℚ, a, b] // α ∈ Λ ∧ IsQuadraticDatum t n α}

def IsOptimalDatum (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b]) : Prop :=
  ∀ x ∈ Λ, (∃ c d : ℚ, x = c • (1 : ℍ[ℚ, a, b]) + d • α) →
    ∃ p q : ℤ, x = (p : ℚ) • (1 : ℍ[ℚ, a, b]) + (q : ℚ) • α

def UnitConj {Λ : Submodule ℤ ℍ[ℚ, a, b]} {t n : ℤ} (d d' : EmbeddingDatum Λ t n) : Prop :=
  ∃ u : ℍ[ℚ, a, b], IsUnitOf Λ u ∧ d'.1 * u = u * d.1

def HasEmbeddingConductor (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b]) (f : ℕ) : Prop :=
  (∀ x ∈ Λ, (∃ c e : ℚ, x = c • (1 : ℍ[ℚ, a, b]) + e • α) →
      ∃ p q : ℤ, (f : ℚ) • x = (p : ℚ) • (1 : ℍ[ℚ, a, b]) + (q : ℚ) • α) ∧
    (∀ g : ℕ, 0 < g → g < f →
      ¬ (∀ x ∈ Λ, (∃ c e : ℚ, x = c • (1 : ℍ[ℚ, a, b]) + e • α) →
        ∃ p q : ℤ, (g : ℚ) • x = (p : ℚ) • (1 : ℍ[ℚ, a, b]) + (q : ℚ) • α))

abbrev EmbeddingDatum.HasConductor {Λ : Submodule ℤ ℍ[ℚ, a, b]} {t n : ℤ}
    (d : EmbeddingDatum Λ t n) (f : ℕ) : Prop :=
  HasEmbeddingConductor Λ d.1 f

def EmbeddingClassSet (Λ : Submodule ℤ ℍ[ℚ, a, b]) (t n : ℤ) : Type :=
  Quot (UnitConj (Λ := Λ) (t := t) (n := n))

noncomputable def condEmbeddingCount (Λ : Submodule ℤ ℍ[ℚ, a, b]) (t n : ℤ) (f : ℕ) : ℕ :=
  Nat.card {c : EmbeddingClassSet Λ t n //
    ∃ d : EmbeddingDatum Λ t n, Quot.mk _ d = c ∧ d.HasConductor f}

theorem isQuadraticDatum_iff {t n : ℤ} {α : ℍ[ℚ, a, b]} :
    IsQuadraticDatum t n α ↔ α * α - (t : ℚ) • α + (n : ℚ) • (1 : ℍ[ℚ, a, b]) = 0 :=
  Iff.rfl

section ReducedNorm

variable {R : Type*} [CommRing R] {a b : R}

def nrd (x : ℍ[R, a, b]) : R :=
  x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2

def trd (x : ℍ[R, a, b]) : R := 2 * x.re

@[simp] theorem nrd_mk (x₀ x₁ x₂ x₃ : R) :
    nrd (⟨x₀, x₁, x₂, x₃⟩ : ℍ[R, a, b]) = x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 := rfl

@[simp] theorem trd_mk (x₀ x₁ x₂ x₃ : R) :
    trd (⟨x₀, x₁, x₂, x₃⟩ : ℍ[R, a, b]) = 2 * x₀ := rfl

@[simp] theorem nrd_zero : nrd (0 : ℍ[R, a, b]) = 0 := by simp [nrd]
@[simp] theorem nrd_one : nrd (1 : ℍ[R, a, b]) = 1 := by simp [nrd]
@[simp] theorem nrd_neg (x : ℍ[R, a, b]) : nrd (-x) = nrd x := by simp [nrd]
@[simp] theorem nrd_star (x : ℍ[R, a, b]) : nrd (star x) = nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; simp only [star_mk, nrd_mk]; ring
@[simp] theorem nrd_coe (r : R) : nrd ((r : R) : ℍ[R, a, b]) = r ^ 2 := by simp [nrd]

theorem mul_star_eq_coe_nrd (x : ℍ[R, a, b]) : x * star x = ((nrd x : R) : ℍ[R, a, b]) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp only [star_mk, mk_mul_mk, nrd_mk, re_coe, imI_coe, imJ_coe, imK_coe] <;> ring

theorem star_mul_eq_coe_nrd (x : ℍ[R, a, b]) : star x * x = ((nrd x : R) : ℍ[R, a, b]) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp only [star_mk, mk_mul_mk, nrd_mk, re_coe, imI_coe, imJ_coe, imK_coe] <;> ring

theorem add_star_eq_coe_trd (x : ℍ[R, a, b]) : x + star x = ((trd x : R) : ℍ[R, a, b]) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp only [star_mk, mk_add_mk, trd_mk, re_coe, imI_coe, imJ_coe, imK_coe] <;> ring

end ReducedNorm

variable {a b : ℚ}

abbrev ClassSet (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Type :=
  DoubleCoset.Quotient
    (((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range :
        Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (U : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)

namespace ClassSet

variable {U U' : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}

variable (U) in

abbrev mk (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ClassSet U :=
  DoubleCoset.mk (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range U x

theorem mk_surjective : Function.Surjective (mk U) := Quotient.mk''_surjective

def map (h : U ≤ U') : ClassSet U → ClassSet U' :=
  Quotient.map' id fun x y hxy => by
    obtain ⟨c, hc, d, hd, rfl⟩ := DoubleCoset.rel_iff.mp hxy
    exact DoubleCoset.rel_iff.mpr ⟨c, hc, d, h hd, rfl⟩

@[simp] theorem map_mk (h : U ≤ U') (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    map h (mk U x) = mk U' x := rfl

theorem map_surjective (h : U ≤ U') : Function.Surjective (map h) := by
  rintro ⟨x⟩; exact ⟨mk U x, rfl⟩

theorem mk_mul_of_mem (x u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hu : u ∈ U) :
    mk U (x * u) = mk U x :=
  (DoubleCoset.eq.mpr ⟨1, one_mem _, u, hu, by rw [one_mul]⟩).symm

theorem mk_diagonal_mul (δ : (ℍ[ℚ, a, b])ˣ) (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    mk U (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x) = mk U x :=
  (DoubleCoset.eq.mpr
    ⟨Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ, MonoidHom.mem_range.mpr ⟨δ, rfl⟩, 1,
      one_mem _, by rw [mul_one]⟩).symm

end ClassSet

section HeckeKernel

def HeckeIncidence (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (y : ClassSet U) : Type :=
  {c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U //
    ∃ h ∈ S, (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U) = c ∧ ClassSet.mk U (x * h) = y}

def heckeKernel (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (x y : ClassSet U) : ℤ :=
  Nat.card (HeckeIncidence U S x.out y)

def heckeIncidenceEquiv (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hS : ∀ u ∈ U, ∀ s ∈ S, u * s ∈ S)
    (x u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hu : u ∈ U) (y : ClassSet U) :
    HeckeIncidence U S (x * u) y ≃ HeckeIncidence U S x y where
  toFun c := ⟨u • c.1, by
    obtain ⟨h, hh, hc, hy⟩ := c.2
    refine ⟨u * h, hS u hu h hh, ?_, ?_⟩
    · rw [← hc]; rfl
    · rwa [← mul_assoc]⟩
  invFun c := ⟨u⁻¹ • c.1, by
    obtain ⟨h, hh, hc, hy⟩ := c.2
    refine ⟨u⁻¹ * h, hS u⁻¹ (inv_mem hu) h hh, ?_, ?_⟩
    · rw [← hc]; rfl
    · rwa [← mul_assoc, mul_inv_cancel_right]⟩
  left_inv c := Subtype.ext (by simp)
  right_inv c := Subtype.ext (by simp)

theorem heckeKernel_mk (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hS : ∀ u ∈ U, ∀ s ∈ S, u * s ∈ S)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (y : ClassSet U) :
    heckeKernel U S (ClassSet.mk U x) y = Nat.card (HeckeIncidence U S x y) := by
  obtain ⟨δ, hδ, u, hu, hout⟩ :=
    DoubleCoset.mk_out_eq_mul (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range U x
  unfold heckeKernel
  rw [show (ClassSet.mk U x).out = δ * x * u from hout]
  have e1 : HeckeIncidence U S (δ * x * u) y ≃ HeckeIncidence U S (δ * x) y :=
    heckeIncidenceEquiv U S hS (δ * x) u hu y
  have e2 : HeckeIncidence U S (δ * x) y ≃ HeckeIncidence U S x y := by
    refine Equiv.subtypeEquivRight fun c => ?_
    obtain ⟨δ', rfl⟩ := MonoidHom.mem_range.mp hδ
    simp only [mul_assoc, ClassSet.mk_diagonal_mul]
  rw [Nat.card_congr (e1.trans e2)]

end HeckeKernel

section Level

def primeHeckeSet (Λ : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) :
    Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  {h | (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ ∧
    (ℓ : ℚ) • ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ ∧
    ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
        ∉ Submodule.finiteAdeleBox Λ ∧
    (ℓ : ℚ)⁻¹ • (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∉ Submodule.finiteAdeleBox Λ}

theorem mem_primeHeckeSet_iff (Λ : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ)
    (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    h ∈ primeHeckeSet Λ ℓ ↔
      (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ ∧
      (ℓ : ℚ) • ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
          ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ ∧
      ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
          ∉ Submodule.finiteAdeleBox Λ ∧
      (ℓ : ℚ)⁻¹ • (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∉ Submodule.finiteAdeleBox Λ :=
  Iff.rfl

def levelHeckeSet (Λ P : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) :
    Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  primeHeckeSet Λ ℓ ∩
    {h | (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) - 1 ∈ Submodule.finiteAdeleBox P}

theorem mem_levelHeckeSet_iff (Λ P : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ)
    (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    h ∈ levelHeckeSet Λ P ℓ ↔
      h ∈ primeHeckeSet Λ ℓ ∧
        (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) - 1 ∈ Submodule.finiteAdeleBox P :=
  Iff.rfl

def congruenceLevel (Λ P : Submodule ℤ ℍ[ℚ, a, b]) :
    Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ where
  carrier := {u | u ∈ Submodule.finiteIdeleStabilizer Λ ∧ u ∈ Submodule.finiteIdeleStabilizer P ∧
    ∀ x ∈ Submodule.finiteAdeleBox Λ,
      (u : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * x - x ∈ Submodule.finiteAdeleBox P}
  one_mem' := ⟨one_mem _, one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro u v ⟨huΛ, huP, hu⟩ ⟨hvΛ, hvP, hv⟩
    refine ⟨mul_mem huΛ hvΛ, mul_mem huP hvP, fun x hx => ?_⟩
    have h1 : (u : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * ((v : _) * x - x) ∈
        Submodule.finiteAdeleBox P := by
      have hmem : (u : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * ((v : _) * x - x) ∈
          u • ((Submodule.finiteAdeleBox P : AddSubgroup _) :
            Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
        Set.smul_mem_smul_set (hv x hx)
      rwa [(Submodule.mem_finiteIdeleStabilizer_iff P u).mp huP] at hmem
    have h2 := hu x hx
    have : ((u * v : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
          ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * x - x
        = (u : _) * ((v : _) * x - x) + ((u : _) * x - x) := by
      rw [Units.val_mul, mul_sub, mul_assoc]; abel
    rw [this]
    exact add_mem h1 h2
  inv_mem' := by
    rintro u ⟨huΛ, huP, hu⟩
    refine ⟨inv_mem huΛ, inv_mem huP, fun x hx => ?_⟩
    have hy : ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : _) * x ∈
        Submodule.finiteAdeleBox Λ := by
      have hmem : ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : _) * x ∈
          u⁻¹ • ((Submodule.finiteAdeleBox Λ : AddSubgroup _) :
            Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
        Set.smul_mem_smul_set hx
      rwa [(Submodule.mem_finiteIdeleStabilizer_iff Λ u⁻¹).mp (inv_mem huΛ)] at hmem
    have h := hu _ hy
    rw [← mul_assoc, Units.mul_inv, one_mul] at h
    rw [← neg_sub]
    exact neg_mem h

theorem mem_congruenceLevel_iff (Λ P : Submodule ℤ ℍ[ℚ, a, b])
    (u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    u ∈ congruenceLevel Λ P ↔
      u ∈ Submodule.finiteIdeleStabilizer Λ ∧ u ∈ Submodule.finiteIdeleStabilizer P ∧
        ∀ x ∈ Submodule.finiteAdeleBox Λ,
          (u : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * x - x ∈ Submodule.finiteAdeleBox P :=
  Iff.rfl

theorem congruenceLevel_le (Λ P : Submodule ℤ ℍ[ℚ, a, b]) :
    congruenceLevel Λ P ≤ Submodule.finiteIdeleStabilizer Λ := fun _ hu => hu.1

def normIdeal (Λ : Submodule ℤ ℍ[ℚ, a, b]) (q : ℕ) : Submodule ℤ ℍ[ℚ, a, b] :=
  Submodule.span ℤ {w | ∃ x ∈ Λ, ∃ y ∈ Λ, ∃ z ∈ Λ, (∃ m : ℤ, nrd y = (q : ℚ) * m) ∧ w = x * y * z}

theorem mul_mul_mem_normIdeal {Λ : Submodule ℤ ℍ[ℚ, a, b]} {q : ℕ} {x y z : ℍ[ℚ, a, b]}
    (hx : x ∈ Λ) (hy : y ∈ Λ) (hz : z ∈ Λ) (m : ℤ) (hm : nrd y = (q : ℚ) * m) :
    x * y * z ∈ normIdeal Λ q :=
  Submodule.subset_span ⟨x, hx, y, hy, z, hz, ⟨m, hm⟩, rfl⟩

theorem IsOrder.normIdeal_le {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (q : ℕ) :
    normIdeal Λ q ≤ Λ := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, hx, y, hy, z, hz, -, rfl⟩
  exact hΛ.mul_mem (hΛ.mul_mem hx hy) hz

theorem IsOrder.mul_mem_normIdeal {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {q : ℕ}
    {x w : ℍ[ℚ, a, b]} (hx : x ∈ Λ) (hw : w ∈ normIdeal Λ q) : x * w ∈ normIdeal Λ q := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x', hx', y, hy, z, hz, ⟨m, hm⟩, rfl⟩ := hw
    simpa only [mul_assoc] using mul_mul_mem_normIdeal (hΛ.mul_mem hx hx') hy hz m hm
  | zero => simp
  | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
  | smul n u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ n hu

theorem IsOrder.mul_mem_normIdeal_right {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {q : ℕ}
    {w z : ℍ[ℚ, a, b]} (hw : w ∈ normIdeal Λ q) (hz : z ∈ Λ) : w * z ∈ normIdeal Λ q := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, y, hy, z', hz', ⟨m, hm⟩, rfl⟩ := hw
    simpa only [mul_assoc] using mul_mul_mem_normIdeal hx hy (hΛ.mul_mem hz' hz) m hm
  | zero => simp
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | smul n u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ n hu

theorem IsOrder.natCast_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (n : ℕ) :
    (n : ℍ[ℚ, a, b]) ∈ Λ := by
  simpa using Submodule.smul_mem Λ (n : ℤ) hΛ.one_mem

theorem IsOrder.natCast_mul_mem_normIdeal {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (q : ℕ)
    {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : (q : ℍ[ℚ, a, b]) * x ∈ normIdeal Λ q := by
  have h := mul_mul_mem_normIdeal (q := q) hΛ.one_mem (hΛ.natCast_mem q) hx (q : ℤ) (by
    rw [show (q : ℍ[ℚ, a, b]) = ((q : ℚ) : ℍ[ℚ, a, b]) by norm_cast, nrd_coe]; push_cast; ring)
  simpa using h

theorem IsOrder.natCast_smul_mem_normIdeal {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (q : ℕ)
    {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : ((q : ℕ) : ℤ) • x ∈ normIdeal Λ q := by
  have h := hΛ.natCast_mul_mem_normIdeal q hx
  rwa [show (q : ℍ[ℚ, a, b]) * x = ((q : ℕ) : ℤ) • x by
    rw [zsmul_eq_mul, Int.cast_natCast]] at h

end Level

section FiniteIdele

variable {a b : ℚ}

def finiteAdeleQuadSubring (α : ℍ[ℚ, a, b]) : Subring (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  Subring.closure
    ({α ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)} ∪
      Set.range (fun r : FiniteAdeleRing (𝓞 ℚ) ℚ => (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r))

def finiteIdeleQuadUnits (α : ℍ[ℚ, a, b]) : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ
  where
  carrier := {u | (u : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ finiteAdeleQuadSubring α ∧
    ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
      ∈ finiteAdeleQuadSubring α}
  one_mem' := by
    constructor
    · rw [Units.val_one]; exact one_mem _
    · rw [inv_one, Units.val_one]; exact one_mem _
  mul_mem' := by
    intro x y hx hy
    constructor
    · rw [Units.val_mul]; exact mul_mem hx.1 hy.1
    · rw [mul_inv_rev, Units.val_mul]; exact mul_mem hy.2 hx.2
  inv_mem' := by
    intro x hx
    exact ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

def quadUnitsDiagonal (α : ℍ[ℚ, a, b]) : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range ⊓ finiteIdeleQuadUnits α

def embeddingSetOrd (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b]) :
    Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  {β | ∀ y ∈ finiteAdeleQuadSubring α,
    ((β⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
      * y * β
        ∈ (Submodule.finiteAdeleBox Λ : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))
      ↔ y ∈ (Submodule.finiteAdeleBox Λ : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))}

def IdelicEmbeddingClassSet (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b]) : Type :=
  {q : DoubleCoset.Quotient
      ((quadUnitsDiagonal α : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Set (ℍ[ℚ, a,
        b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
      ((Submodule.finiteIdeleStabilizer Λ : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) //
    ∃ x ∈ embeddingSetOrd Λ α,
      DoubleCoset.mk (quadUnitsDiagonal α) (Submodule.finiteIdeleStabilizer Λ) x = q}

def EmbeddingClassFibre (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b])
    (β : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Type :=
  {q : DoubleCoset.Quotient
      ((quadUnitsDiagonal α : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Set (ℍ[ℚ, a,
        b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
      ((Submodule.finiteIdeleStabilizer Λ : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) //
    ∃ x ∈ embeddingSetOrd Λ α,
      DoubleCoset.mk (quadUnitsDiagonal α) (Submodule.finiteIdeleStabilizer Λ) x = q ∧
      (DoubleCoset.mk (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range
          (Submodule.finiteIdeleStabilizer Λ) x :
        DoubleCoset.Quotient
          (((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ]
            FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
          ((Submodule.finiteIdeleStabilizer Λ : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ)
            ℚ)ˣ) : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ))
        = DoubleCoset.mk (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range
          (Submodule.finiteIdeleStabilizer Λ) β}

end FiniteIdele

end QuaternionAlgebra

end

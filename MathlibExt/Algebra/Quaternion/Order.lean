/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_QuaternionAlgebra_Order.lean`,
`Definitions/Def_QuaternionAlgebra_EichlerOrder.lean`
and
`Definitions/Def_QuaternionAlgebra_BaseChange.lean`
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

public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.Quaternion
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion

@[expose] public section

open scoped Quaternion TensorProduct

namespace QuaternionAlgebra

variable {a b : ℚ}

/-- A `ℤ`-order in a rational quaternion algebra: a `ℤ`-submodule containing
`1`, closed under multiplication, spanning the whole algebra over `ℚ`, and
finitely generated as a `ℤ`-module. -/
structure IsOrder (Λ : Submodule ℤ ℍ[ℚ, a, b]) : Prop where
  one_mem : (1 : ℍ[ℚ, a, b]) ∈ Λ
  mul_mem : ∀ ⦃x y : ℍ[ℚ, a, b]⦄, x ∈ Λ → y ∈ Λ → x * y ∈ Λ
  spanTop : Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) = ⊤
  fg : Λ.FG

/-- `u` is a unit of the submodule `Λ` with inverse again in `Λ`. -/
def IsUnitOf (Λ : Submodule ℤ ℍ[ℚ, a, b]) (u : ℍ[ℚ, a, b]) : Prop :=
  u ∈ Λ ∧ ∃ v ∈ Λ, u * v = 1 ∧ v * u = 1

/-- The quadratic datum `α² - tα + n = 0` over `ℤ`. -/
def IsQuadraticDatum (t n : ℤ) (α : ℍ[ℚ, a, b]) : Prop :=
  α * α - (t : ℚ) • α + (n : ℚ) • (1 : ℍ[ℚ, a, b]) = 0

/-- An embedding datum: an element `α` of `Λ` satisfying a quadratic datum, with
`1` and `α` linearly independent, so that `X ↦ α` is injective on
`ℤ[X]/(X² - tX + n)`. Unlike the adapted source, this excludes scalar roots,
such as `α = 0` for `t = n = 0`. -/
def EmbeddingDatum (Λ : Submodule ℤ ℍ[ℚ, a, b]) (t n : ℤ) : Type :=
  {α : ℍ[ℚ, a, b] // α ∈ Λ ∧ IsQuadraticDatum t n α ∧
    LinearIndependent ℚ ![(1 : ℍ[ℚ, a, b]), α]}

/-- Optimality of `α` in `Λ` at the level of rational `1, α` planes. -/
def IsOptimalDatum (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b]) : Prop :=
  ∀ x ∈ Λ, (∃ c d : ℚ, x = c • (1 : ℍ[ℚ, a, b]) + d • α) →
    ∃ p q : ℤ, x = (p : ℚ) • (1 : ℍ[ℚ, a, b]) + (q : ℚ) • α

/-- Conjugacy of embedding data by a unit of `Λ`. -/
def UnitConj {Λ : Submodule ℤ ℍ[ℚ, a, b]} {t n : ℤ}
    (d d' : EmbeddingDatum Λ t n) : Prop :=
  ∃ u : ℍ[ℚ, a, b], IsUnitOf Λ u ∧ d'.1 * u = u * d.1

/-- `f` is the embedding conductor of `α` in `Λ`: the least positive `f` with
`f • x ∈ ℤ + ℤα` for every `x ∈ Λ` in the rational span of `1` and `α`.
Unlike the adapted source, `f` must be positive: for `f = 0` the other two
clauses hold for every `α`. -/
def HasEmbeddingConductor (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b])
    (f : ℕ) : Prop :=
  0 < f ∧ (∀ x ∈ Λ, (∃ c e : ℚ, x = c • (1 : ℍ[ℚ, a, b]) + e • α) →
      ∃ p q : ℤ, (f : ℚ) • x = (p : ℚ) • (1 : ℍ[ℚ, a, b]) + (q : ℚ) • α) ∧
    (∀ g : ℕ, 0 < g → g < f →
      ¬ (∀ x ∈ Λ, (∃ c e : ℚ, x = c • (1 : ℍ[ℚ, a, b]) + e • α) →
        ∃ p q : ℤ, (g : ℚ) • x = (p : ℚ) • (1 : ℍ[ℚ, a, b]) + (q : ℚ) • α))

/-- The conductor predicate for an embedding datum. -/
abbrev EmbeddingDatum.HasConductor {Λ : Submodule ℤ ℍ[ℚ, a, b]} {t n : ℤ}
    (d : EmbeddingDatum Λ t n) (f : ℕ) : Prop :=
  HasEmbeddingConductor Λ d.1 f

/-- Conjugacy classes of embedding data. -/
def EmbeddingClassSet (Λ : Submodule ℤ ℍ[ℚ, a, b]) (t n : ℤ) : Type :=
  Quot (UnitConj (Λ := Λ) (t := t) (n := n))

/-- Number of embedding classes with conductor `f`. -/
noncomputable def condEmbeddingCount (Λ : Submodule ℤ ℍ[ℚ, a, b]) (t n : ℤ)
    (f : ℕ) : ℕ :=
  Nat.card {c : EmbeddingClassSet Λ t n //
    ∃ d : EmbeddingDatum Λ t n, Quot.mk _ d = c ∧ d.HasConductor f}

theorem isQuadraticDatum_iff {t n : ℤ} {α : ℍ[ℚ, a, b]} :
    IsQuadraticDatum t n α ↔
      α * α - (t : ℚ) • α + (n : ℚ) • (1 : ℍ[ℚ, a, b]) = 0 :=
  Iff.rfl

theorem exists_natCast_smul_mem_of_mem_span {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {y : ℍ[ℚ, a, b]} (hy : y ∈ Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b])) :
    ∃ n : ℕ, n ≠ 0 ∧ ((n : ℕ) : ℤ) • y ∈ Λ := by
  induction hy using Submodule.span_induction with
  | mem z hz => exact ⟨1, one_ne_zero, by simpa using hz⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨m, hm, hmu⟩ := hu
    obtain ⟨n, hn, hnv⟩ := hv
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [Nat.cast_mul, mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hmu
    · rw [Nat.cast_mul, mul_smul]; exact Submodule.smul_mem _ _ hnv
  | smul c u _ hu =>
    obtain ⟨n, hn, hnu⟩ := hu
    refine ⟨c.den * n, mul_ne_zero c.den_ne_zero hn, ?_⟩
    have hthis : (((c.den * n : ℕ) : ℤ)) • c • u = c.num • (((n : ℕ) : ℤ) • u) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ c.num,
        ← Int.cast_smul_eq_zsmul ℚ ((n : ℕ) : ℤ), smul_smul, smul_smul]
      congr 1
      push_cast
      rw [← Rat.mul_den_eq_num c]
      ring
    rw [hthis]
    exact Submodule.smul_mem _ _ hnu

/-- The intersection of two orders is an order. -/
theorem IsOrder.inf {Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]} (h₁ : IsOrder Λ₁)
    (h₂ : IsOrder Λ₂) : IsOrder (Λ₁ ⊓ Λ₂) :=
  have : Submodule.IsFullLattice ℚ Λ₁ :=
    { toIsLattice := .of_fg ℚ h₁.fg, span_eq_top := h₁.spanTop }
  have : Submodule.IsFullLattice ℚ Λ₂ :=
    { toIsLattice := .of_fg ℚ h₂.fg, span_eq_top := h₂.spanTop }
  { one_mem := ⟨h₁.one_mem, h₂.one_mem⟩
    mul_mem := fun _ _ hx hy => ⟨h₁.mul_mem hx.1 hy.1, h₂.mul_mem hx.2 hy.2⟩
    spanTop := Submodule.IsFullLattice.span_eq_top
    fg := Submodule.IsLattice.fg ℚ (Λ₁ ⊓ Λ₂) }

/-- A maximal order: an order contained in no strictly larger order. -/
def IsMaximalOrder (Λ : Submodule ℤ ℍ[ℚ, a, b]) : Prop :=
  IsOrder Λ ∧ ∀ Λ' : Submodule ℤ ℍ[ℚ, a, b], IsOrder Λ' → Λ ≤ Λ' → Λ' = Λ

theorem IsMaximalOrder.isOrder {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (h : IsMaximalOrder Λ) : IsOrder Λ :=
  h.1

/-- An Eichler order of level `N`: an intersection of two maximal orders
whose additive index in the first is `N`. -/
def IsEichlerOrder (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ) : Prop :=
  ∃ Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b], IsMaximalOrder Λ₁ ∧ IsMaximalOrder Λ₂ ∧
    Λ = Λ₁ ⊓ Λ₂ ∧ Λ.toAddSubgroup.relIndex Λ₁.toAddSubgroup = N

theorem IsEichlerOrder.isOrder {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (h : IsEichlerOrder Λ N) : IsOrder Λ := by
  obtain ⟨Λ₁, Λ₂, h₁, h₂, rfl, -⟩ := h
  exact h₁.isOrder.inf h₂.isOrder

theorem IsEichlerOrder.exists_le_isMaximalOrder {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {N : ℕ} (h : IsEichlerOrder Λ N) :
    ∃ Λ₁ : Submodule ℤ ℍ[ℚ, a, b], IsMaximalOrder Λ₁ ∧ Λ ≤ Λ₁ ∧
      Λ.toAddSubgroup.relIndex Λ₁.toAddSubgroup = N := by
  obtain ⟨Λ₁, Λ₂, h₁, -, rfl, hN⟩ := h
  exact ⟨Λ₁, h₁, inf_le_left, hN⟩

variable (a b) in
/-- Definite ramification exactly at `q`, in the stated local form. -/
def IsDefiniteRamifiedExactlyAt (q : ℕ) : Prop :=
  a < 0 ∧ b < 0 ∧
    ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
      (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) ↔
        ((q : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal)

theorem IsDefiniteRamifiedExactlyAt.neg_left {q : ℕ}
    (h : IsDefiniteRamifiedExactlyAt a b q) : a < 0 :=
  h.1

theorem IsDefiniteRamifiedExactlyAt.neg_right {q : ℕ}
    (h : IsDefiniteRamifiedExactlyAt a b q) : b < 0 :=
  h.2.1

end QuaternionAlgebra

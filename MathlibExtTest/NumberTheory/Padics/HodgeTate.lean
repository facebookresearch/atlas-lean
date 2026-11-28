/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.Padics.HodgeTate

/-!
# Tests for the Hodge–Tate ring

The Galois action on `B_HT = ℂ_p[t, t⁻¹]` on monomials and coefficients, its group laws and its
grading; `B_HT` is a domain, its invariants under `Gal(ℚ̄_p / ℚ_p)` are the constants in `ℚ_p`,
`t` is not invariant, and `B_HT^{G_K}` has degree `[K : ℚ_p]` over `ℚ_p`; regularity gives an
injective comparison map, `dim_K D_HT(V) ≤ dim V` and units from stable lines.
-/

open LaurentPolynomial MathlibExt.AlgebraicGeometry.HodgeTateComparison PadicComplex
  Representation
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

/-! ### The action on `B_HT` -/

/-- `B_HT` is a domain: condition (i) of regularity is Mathlib's instance. -/
example : IsDomain ℂ_[p][T;T⁻¹] := inferInstance

/-- `σ (c tⁿ) = σ(c) χ(σ)ⁿ tⁿ`. -/
example (σ : Galois p) (c : ℂ_[p]) (n : ℤ) :
    hodgeTateAction p σ (C c * T n) =
      C (cyclotomicScalar p σ ^ n • completionGalois p σ c) * T n :=
  hodgeTateAction_C_mul_T p σ c n

/-- `σ(t) = χ(σ) t` and `σ(t⁻¹) = χ(σ)⁻¹ t⁻¹`. -/
example (σ : Galois p) :
    hodgeTateAction p σ (T 1) = cyclotomicScalar p σ • T 1 ∧
      hodgeTateAction p σ (T (-1)) = (cyclotomicScalar p σ)⁻¹ • T (-1) := by
  simp

/-- The coefficient of `t²` in `σ f` is `χ(σ)² σ(f₂)`. -/
example (σ : Galois p) (f : ℂ_[p][T;T⁻¹]) :
    (hodgeTateAction p σ f).coeff 2 = cyclotomicScalar p σ ^ (2 : ℤ) •
      completionGalois p σ (f.coeff 2) :=
  coeff_hodgeTateAction p σ f 2

/-- The action is a group action by automorphisms: `στ` acts as `σ ∘ τ`, and `σ⁻¹ ∘ σ = id`. -/
example (σ τ : Galois p) (f : ℂ_[p][T;T⁻¹]) :
    hodgeTateAction p (σ * τ) f = hodgeTateAction p σ (hodgeTateAction p τ f) ∧
      hodgeTateAction p σ⁻¹ (hodgeTateAction p σ f) = f := by
  refine ⟨by rw [map_mul, AlgHom.mul_apply], ?_⟩
  rw [← AlgHom.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgHom.one_apply]

/-- The action preserves the grading: `σ` maps `ℂ_p tⁱ` to itself. -/
example (σ : Galois p) (c : ℂ_[p]) (i : ℤ) :
    hodgeTateAction p σ (AddMonoidAlgebra.single i c) ∈ AddMonoidAlgebra.grade ℂ_[p] i :=
  (hodgeTateAction_mem_grade_iff p σ _ i).2 (AddMonoidAlgebra.single_mem_grade i c)

/-! ### The invariants of `B_HT` -/

/-- `B_HT ^ Gal(ℚ̄_p / ℚ_p) = ℚ_p`. -/
example (f : ℂ_[p][T;T⁻¹]) (hf : ∀ σ : Galois p, hodgeTateAction p σ f = f) :
    ∃ q : ℚ_[p], f = C (algebraMap ℚ_[p] ℂ_[p] q) := by
  obtain ⟨y, rfl⟩ := (forall_hodgeTateAction_eq_self_iff p ⊥ f).1 fun σ _ => hf σ
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.1 y.2
  refine ⟨q, ?_⟩
  change C ((y : PadicAlgCl p) : ℂ_[p]) = _
  rw [← hq, PadicComplex.coe_eq, ← IsScalarTower.algebraMap_apply]

/-- `t` is not invariant under `Gal(ℚ̄_p / K)`. -/
example (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    (T 1 : ℂ_[p][T;T⁻¹]) ∉
      fixedSubalgebra ℂ_[p][T;T⁻¹] (hodgeTateAction p) K.fixingSubgroup := by
  intro h
  obtain ⟨y, hy⟩ := (forall_hodgeTateAction_eq_self_iff p K _).1 (mem_fixedSubalgebra.1 h)
  have := congrArg (fun f : ℂ_[p][T;T⁻¹] => f.coeff 1) hy
  simp at this

/-- `B_HT^{G_K} ≅ K`, so it has degree `[K : ℚ_p]` over `ℚ_p`. -/
example (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    Module.finrank ℚ_[p]
        (fixedSubalgebra ℂ_[p][T;T⁻¹] (hodgeTateAction p) K.fixingSubgroup) =
      Module.finrank ℚ_[p] K :=
  (hodgeTateFixedSubalgebraEquiv p K).toLinearEquiv.finrank_eq.symm

/-! ### Regularity -/

/-- For every representation, the comparison map `B_HT ⊗_K D_HT(V) → B_HT ⊗_{ℚ_p} V` is
injective, and `dim_K D_HT(V) ≤ dim_{ℚ_p} V`. -/
example (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (ρ : Representation ℚ_[p] (Galois p) V) [FiniteDimensional ℚ_[p] V] :
    Function.Injective (ρ.comparison (hodgeTateAction p) K.fixingSubgroup) ∧
      Module.finrank (fixedSubalgebra ℂ_[p][T;T⁻¹] (hodgeTateAction p) K.fixingSubgroup)
        (ρ.periods (hodgeTateAction p) K.fixingSubgroup) ≤ Module.finrank ℚ_[p] V :=
  ⟨(isRegularPeriodRing_hodgeTateAction p K).comparison_injective ρ,
    (isRegularPeriodRing_hodgeTateAction p K).finrank_periods_le ρ⟩

/-- Condition (iii): `t³` spans a `Gal(ℚ̄_p / K)`-stable `ℚ_p`-line, so it is a unit. -/
example (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    IsUnit (T 3 : ℂ_[p][T;T⁻¹]) :=
  (isRegularPeriodRing_hodgeTateAction p K).isUnit_of_forall_mem_span _ (isUnit_T 3).ne_zero
    fun σ _ => Submodule.mem_span_singleton.2 ⟨cyclotomicScalar p σ ^ (3 : ℤ), by simp⟩

/-- An element spanning a `Gal(ℚ̄_p / K)`-stable `ℂ_p`-line, with a nonzero coefficient of `t²`,
is the monomial `b₂ t²`. -/
example (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] {b : ℂ_[p][T;T⁻¹]}
    (hb : b.coeff 2 ≠ 0) (h : ∀ σ ∈ K.fixingSubgroup, ∃ u : ℂ_[p], hodgeTateAction p σ b = u • b) :
    b = C (b.coeff 2) * T 2 := by
  rw [← single_eq_C_mul_T]
  exact eq_single_of_forall_exists_smul_eq p K hb h

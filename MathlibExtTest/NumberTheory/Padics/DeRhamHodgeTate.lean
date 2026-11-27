/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.Padics.DeRhamHodgeTate

/-!
# Tests for de Rham representations being Hodge–Tate

The filtration of `D_dR(V)` is finite, `dim_K D_dR(V) = Σᵢ dim_K gr^i D_dR(V)`,
`dim_K gr^i D_dR(V) ≤ h_{-i}` and `dim_K D_dR(V) ≤ dim_K D_HT(V)`; a de Rham representation is
Hodge–Tate with `dim_K gr^i D_dR(V) = h_{-i}` and `gr^i D_dR(V) ≅ (ℂ_p(i) ⊗ V)^{G_K}`; `ℚ_p(1)` is
de Rham, `t⁻¹ ⊗ 1 ∈ D_dR(ℚ_p(1))`, and its filtration jumps at `-1`.
-/

open LaurentPolynomial MathlibExt.AlgebraicGeometry.HodgeTateComparison PadicComplexInt
  Representation
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

local notation "𝔹⁺" => BDeRhamPlus 𝓞_ℂ_[p] p
local notation "𝔹" => BDeRham 𝓞_ℂ_[p] p
local notation "𝕥" => logTeichmuller p (untilt_epsilon p)

/-- The filtration of `D_dR(V)` is finite. -/
example (ρ : Representation ℚ_[p] (Galois p) V) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] V] :
    (∃ a, ∀ i ≤ a, ρ.deRhamFiltration K i = ρ.periods (galoisBDeRham p) K.fixingSubgroup) ∧
      ∃ b, ∀ i, b ≤ i → ρ.deRhamFiltration K i = ⊥ :=
  ⟨exists_deRhamFiltration_eq_periods ρ K, exists_deRhamFiltration_eq_bot ρ K⟩

/-- `dim_K D_dR(V) = Σᵢ dim_K gr^i D_dR(V)`, `dim_K gr^i D_dR(V) ≤ h_{-i}`, and
`dim_K D_dR(V) ≤ dim_K D_HT(V)`. -/
example (ρ : Representation ℚ_[p] (Galois p) V) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] V] (i : ℤ) :
    Module.finrank (fixedSubalgebra 𝔹 (galoisBDeRham p) K.fixingSubgroup)
        (ρ.periods (galoisBDeRham p) K.fixingSubgroup) =
      ∑ᶠ i, Module.finrank (fixedSubalgebra 𝔹 (galoisBDeRham p) K.fixingSubgroup)
        (ρ.deRhamGraded K i) ∧
    Module.finrank (fixedSubalgebra 𝔹 (galoisBDeRham p) K.fixingSubgroup)
        (ρ.deRhamGraded K i) ≤ ρ.hodgeTateNumber K (-i) ∧
    Module.finrank (fixedSubalgebra 𝔹 (galoisBDeRham p) K.fixingSubgroup)
        (ρ.periods (galoisBDeRham p) K.fixingSubgroup) ≤
      Module.finrank (fixedSubalgebra ℂ_[p][T;T⁻¹] (PadicComplex.hodgeTateAction p)
        K.fixingSubgroup) (ρ.periods (PadicComplex.hodgeTateAction p) K.fixingSubgroup) :=
  ⟨finrank_periods_galoisBDeRham_eq_finsum ρ K, finrank_deRhamGraded_le ρ K i,
    finrank_periods_galoisBDeRham_le ρ K⟩

/-- A de Rham representation is Hodge–Tate, `dim_K gr^i D_dR(V) = h_{-i}`, and
`gr^i D_dR(V) → (ℂ_p(i) ⊗ V)^{G_K}` is bijective. -/
example (ρ : Representation ℚ_[p] (Galois p) V) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (h : ρ.IsDeRham K) (i : ℤ) :
    ρ.IsHodgeTate K ∧
      Module.finrank (fixedSubalgebra 𝔹 (galoisBDeRham p) K.fixingSubgroup)
        (ρ.deRhamGraded K i) = ρ.hodgeTateNumber K (-i) ∧
      Function.Bijective (deRhamGradedToTwistPeriods ρ K i) :=
  ⟨h.isHodgeTate, h.finrank_deRhamGraded i, h.deRhamGradedToTwistPeriods_bijective i⟩

/-- `ℚ_p(1)` is de Rham, hence Hodge–Tate, `t⁻¹ ⊗ 1 ∈ D_dR(ℚ_p(1))`, and
`gr^i D_dR(ℚ_p(1))` is one-dimensional for `i = -1` and zero for `i = 0`. -/
example (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    (cyclotomic p).IsDeRham K ∧ (cyclotomic p).IsHodgeTate K ∧
      (algebraMap 𝔹⁺ 𝔹 𝕥 ^ (-1 : ℤ)) ⊗ₜ[ℚ_[p]] (1 : ℚ_[p]) ∈
        (cyclotomic p).periods (galoisBDeRham p) K.fixingSubgroup ∧
      Module.finrank (fixedSubalgebra 𝔹 (galoisBDeRham p) K.fixingSubgroup)
        ((cyclotomic p).deRhamGraded K (-1)) = 1 ∧
      Module.finrank (fixedSubalgebra 𝔹 (galoisBDeRham p) K.fixingSubgroup)
        ((cyclotomic p).deRhamGraded K 0) = 0 := by
  refine ⟨isDeRham_cyclotomic K, (isDeRham_cyclotomic K).isHodgeTate,
    zpow_neg_one_tmul_mem_periods_cyclotomic K, ?_, ?_⟩ <;>
    simp [finrank_deRhamGraded_cyclotomic]

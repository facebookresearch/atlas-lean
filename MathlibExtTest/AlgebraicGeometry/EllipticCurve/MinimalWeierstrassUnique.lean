/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.MinimalWeierstrassUnique
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Tests for `MathlibExt.AlgebraicGeometry.EllipticCurve.MinimalWeierstrassUnique`

Concrete instances over the `2`-adic integers `ℤ_[2] ⊆ ℚ_[2]`:

* the curve `y² + y = x³ - x` (discriminant `37`, a unit in `ℤ_[2]`) is minimal, so every change
  of variables to another minimal equation is defined over `ℤ_[2]`;
* the singular curve `y² = x³` shows that ellipticity cannot be dropped: it is minimal, the
  scaling by `u = 2` maps it to itself, yet `u = 2` is not a unit of `ℤ_[2]`.
-/

@[expose] public section

open WeierstrassCurve IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

namespace MinimalWeierstrassUniqueTest

#check @WeierstrassCurve.valuation_Δ_le_of_isMinimal
#check @WeierstrassCurve.valuation_Δ_eq_of_isMinimal
#check @WeierstrassCurve.valuation_u_eq_one_of_isMinimal
#check @WeierstrassCurve.exists_unit_of_valuation_eq_one
#check @WeierstrassCurve.exists_unit_eq_u_of_isMinimal
#check @WeierstrassCurve.exists_baseChange_eq_of_isMinimal
#check @WeierstrassCurve.exists_map_eq_of_isMinimal
#check @WeierstrassCurve.isIntegral_baseChange_smul
#check @WeierstrassCurve.valuation_Δ_baseChange_smul
#check @WeierstrassCurve.isMinimal_of_valuation_Δ_eq_one
#check @WeierstrassCurve.isMinimal_baseChange_smul
#check @WeierstrassCurve.isMinimal_smul_iff
#check @WeierstrassCurve.span_u_eq_span_one_of_isMinimal

/-- The integral equation `y² + y = x³ - x` over `ℤ_[2]`. -/
noncomputable def E₀ : WeierstrassCurve ℤ_[2] := ⟨0, 0, 1, -1, 0⟩

/-- The equation `y² + y = x³ - x` over `ℚ_[2]`. -/
noncomputable def E : WeierstrassCurve ℚ_[2] := E₀.baseChange ℚ_[2]

lemma E₀_Δ : E₀.Δ = 37 := by
  simp only [E₀, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

lemma isUnit_37 : IsUnit (37 : ℤ_[2]) := by
  by_contra h
  have h₁ := PadicInt.not_isUnit_iff.mp h
  have h₂ : ‖((37 : ℤ) : ℤ_[2])‖ < 1 := by exact_mod_cast h₁
  rw [PadicInt.norm_int_lt_one_iff_dvd] at h₂
  norm_num at h₂

instance : IsIntegral ℤ_[2] E := ⟨⟨E₀, rfl⟩⟩

lemma E_Δ : E.Δ = algebraMap ℤ_[2] ℚ_[2] 37 := by
  rw [E, WeierstrassCurve.baseChange, map_Δ, E₀_Δ]

instance : E.IsElliptic := by
  rw [isElliptic_iff, E_Δ]
  exact isUnit_37.map _

lemma valuation_E_Δ : valuation ℚ_[2] (maximalIdeal ℤ_[2]) E.Δ = 1 := by
  rw [E_Δ]
  exact (valuation_eq_one_iff_notMem _).mpr
    ((IsLocalRing.mem_maximalIdeal _).not.mpr (not_not.mpr isUnit_37))

instance : IsMinimal ℤ_[2] E := isMinimal_of_valuation_Δ_eq_one valuation_E_Δ

/-- Any change of variables from `E` to a minimal equation is defined over `ℤ_[2]`. -/
example (C : VariableChange ℚ_[2]) [IsMinimal ℤ_[2] (C • E)] :
    ∃ C' : VariableChange ℤ_[2], C'.baseChange ℚ_[2] = C :=
  exists_baseChange_eq_of_isMinimal E C

example (C : VariableChange ℚ_[2]) [IsMinimal ℤ_[2] (C • E)] :
    ∃ u : ℤ_[2]ˣ, algebraMap ℤ_[2] ℚ_[2] u = C.u :=
  exists_unit_eq_u_of_isMinimal E C

example (C : VariableChange ℚ_[2]) [IsMinimal ℤ_[2] (C • E)] :
    Submodule.span ℤ_[2] {(C.u : ℚ_[2])} = Submodule.span ℤ_[2] {1} :=
  span_u_eq_span_one_of_isMinimal E C

/-- The change of variables `(u, r, s, t) = (-1, 1, 1, 0)` over `ℤ_[2]`. -/
noncomputable def C₁ : VariableChange ℤ_[2] := ⟨-1, 1, 1, 0⟩

/-- `C₁` takes the minimal equation `E` to a minimal equation. -/
example : IsMinimal ℤ_[2] (C₁.baseChange ℚ_[2] • E) := isMinimal_baseChange_smul C₁

example : IsMinimal ℤ_[2] (C₁.baseChange ℚ_[2] • E) :=
  (isMinimal_smul_iff (W := E) _).mpr ⟨C₁, rfl⟩

/-! ### Ellipticity is necessary -/

/-- The singular equation `y² = x³` over `ℚ_[2]`. -/
noncomputable def N : WeierstrassCurve ℚ_[2] := ⟨0, 0, 0, 0, 0⟩

/-- Scaling by `u = 2`. -/
noncomputable def C₂ : VariableChange ℚ_[2] := ⟨Units.mk0 2 two_ne_zero, 0, 0, 0⟩

lemma C₂_smul_N : C₂ • N = N := by
  ext <;> simp [C₂, N, variableChange_def]

instance : IsIntegral ℤ_[2] N :=
  ⟨⟨⟨0, 0, 0, 0, 0⟩, by ext <;> simp [N, WeierstrassCurve.baseChange]⟩⟩

instance : IsMinimal ℤ_[2] N := by
  refine ⟨⟨by simpa using (inferInstance : IsIntegral ℤ_[2] N), fun j hj _ ↦ ?_⟩⟩
  have : IsIntegral ℤ_[2] (j • N) := hj
  rw [← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral, variableChange_Δ]
  simp [N, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]

instance : IsMinimal ℤ_[2] (C₂ • N) := by rw [C₂_smul_N]; infer_instance

/-- Both `N` and `C₂ • N` are minimal, but `C₂` is not defined over `ℤ_[2]`. -/
example : ¬ ∃ C' : VariableChange ℤ_[2], C'.baseChange ℚ_[2] = C₂ := by
  rintro ⟨C', hC'⟩
  have hu : algebraMap ℤ_[2] ℚ_[2] (C'.u : ℤ_[2]) = algebraMap ℤ_[2] ℚ_[2] 2 := by
    have := congrArg (fun C : VariableChange ℚ_[2] ↦ (C.u : ℚ_[2])) hC'
    rw [map_ofNat]
    simpa [VariableChange.baseChange, C₂] using this
  have h2 : (C'.u : ℤ_[2]) = 2 := (IsFractionRing.injective ℤ_[2] ℚ_[2]) hu
  have h₁ := PadicInt.not_isUnit_iff.mpr (show ‖(2 : ℤ_[2])‖ < 1 by
    have : ‖((2 : ℤ) : ℤ_[2])‖ < 1 := by
      rw [PadicInt.norm_int_lt_one_iff_dvd]; norm_num
    exact_mod_cast this)
  exact h₁ (h2 ▸ C'.u.isUnit)

end MinimalWeierstrassUniqueTest

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Height.PrimitiveMahler
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.EReal.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Asymptotic Dobrowolski coefficients

The catalogue's C40b is the supremum of coefficients valid uniformly for all sufficiently large
degrees. Voutier, arXiv:1211.3110v1, Introduction, supplies the polynomial and Mahler-measure
conventions. No finite upper bound or attainment of the supremum is assumed.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.AsymptoticDobrowolski

open NumberField

/-- The Dobrowolski scale, used only for degrees at least three in the coefficient predicate. -/
noncomputable def dobrowolskiScale (d : ℕ) : ℝ :=
  (Real.log (Real.log d) / Real.log d) ^ 3

/-- The source's degree range makes the scale strictly positive. -/
theorem dobrowolskiScale_pos {d : ℕ} (hd : 3 ≤ d) : 0 < dobrowolskiScale d := by
  have hdreal : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog : 1 < Real.log d :=
    (Real.lt_log_iff_exp_lt (by linarith)).mpr (Real.exp_one_lt_three.trans_le hdreal)
  exact pow_pos (div_pos (Real.log_pos hlog) (zero_lt_one.trans hlog)) 3

/-- The degree threshold depends on epsilon and is uniform over eligible algebraic numbers. -/
def IsAsymptoticDobrowolskiCoefficient (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ D : ℕ, 3 ≤ D ∧
    ∀ α : ℂ, IsAlgebraic ℚ α → α ≠ 0 → ¬IsOfFinOrder α →
      D ≤ (minpoly ℚ α).natDegree →
        1 + (c - ε) * dobrowolskiScale (minpoly ℚ α).natDegree ≤
          algebraicMahlerMeasure α

/-- The supremum of all real admissible coefficients. `EReal` supplies bottom for an empty set
and top for an unbounded set; neither finite attainment nor a finite upper bound is built in. -/
noncomputable def asymptoticDobrowolskiConstant : EReal :=
  sSup {x : EReal | ∃ c : ℝ, IsAsymptoticDobrowolskiCoefficient c ∧ x = c}

/-- Every admissible real coefficient is below the extended-real supremum. -/
theorem coe_le_asymptoticDobrowolskiConstant {c : ℝ}
    (hc : IsAsymptoticDobrowolskiCoefficient c) :
    (c : EReal) ≤ asymptoticDobrowolskiConstant :=
  le_sSup ⟨c, hc, rfl⟩

/-- Coefficient zero witnesses nonemptiness using the actual integral-polynomial model. -/
theorem zero_isAsymptoticDobrowolskiCoefficient : IsAsymptoticDobrowolskiCoefficient 0 := by
  intro ε hε
  refine ⟨3, le_rfl, ?_⟩
  intro α _ _ _ hd
  have hscale := (dobrowolskiScale_pos hd).le
  have hmul : (0 - ε) * dobrowolskiScale (minpoly ℚ α).natDegree ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hscale
  exact le_trans (by linarith) (one_le_algebraicMahlerMeasure α)

/-- An upper bound on the supremum is exactly an upper bound on all admissible coefficients. -/
theorem asymptoticDobrowolskiConstant_le_iff {b : EReal} :
    asymptoticDobrowolskiConstant ≤ b ↔
      ∀ c : ℝ, IsAsymptoticDobrowolskiCoefficient c → (c : EReal) ≤ b := by
  constructor
  · intro hb c hc
    exact (coe_le_asymptoticDobrowolskiConstant hc).trans hb
  · intro hb
    apply sSup_le
    rintro x ⟨c, hc, rfl⟩
    exact hb c hc

/-- Epsilon slack closes the admissible set: a real coefficient is admissible exactly when
it is below the extended-real supremum. This also covers an unbounded admissible set. -/
theorem isAsymptoticDobrowolskiCoefficient_iff {c : ℝ} :
    IsAsymptoticDobrowolskiCoefficient c ↔ (c : EReal) ≤ asymptoticDobrowolskiConstant := by
  refine ⟨coe_le_asymptoticDobrowolskiConstant, ?_⟩
  intro hc ε hε
  have hslack : ((c - ε / 2 : ℝ) : EReal) < (c : EReal) := by
    exact_mod_cast (show c - ε / 2 < c by linarith)
  have hbelow : ((c - ε / 2 : ℝ) : EReal) < asymptoticDobrowolskiConstant :=
    hslack.trans_le hc
  obtain ⟨x, ⟨b, hb, rfl⟩, hxb⟩ := lt_sSup_iff.mp hbelow
  have hcb : c - ε / 2 < b := by exact_mod_cast hxb
  obtain ⟨D, hD, hbound⟩ := hb (ε / 2) (half_pos hε)
  refine ⟨D, hD, ?_⟩
  intro α hα hα0 hroot hd
  have hscale := (dobrowolskiScale_pos (hD.trans hd)).le
  have hcoef : c - ε ≤ b - ε / 2 := by linarith
  linarith [mul_le_mul_of_nonneg_right hcoef hscale, hbound α hα hα0 hroot hd]

/-- Epsilon slack and the positive scale make the source's strict bounds equivalent to
the non-strict convention in the coefficient definition. -/
theorem isAsymptoticDobrowolskiCoefficient_iff_strict {c : ℝ} :
    IsAsymptoticDobrowolskiCoefficient c ↔
      ∀ ε : ℝ, 0 < ε → ∃ D : ℕ, 3 ≤ D ∧
        ∀ α : ℂ, IsAlgebraic ℚ α → α ≠ 0 → ¬IsOfFinOrder α →
          D ≤ (minpoly ℚ α).natDegree →
            1 + (c - ε) * dobrowolskiScale (minpoly ℚ α).natDegree <
              algebraicMahlerMeasure α := by
  constructor
  · intro hc ε hε
    obtain ⟨D, hD, hbound⟩ := hc (ε / 2) (half_pos hε)
    refine ⟨D, hD, ?_⟩
    intro α hα hα0 hroot hd
    have hscale := dobrowolskiScale_pos (hD.trans hd)
    have hmul := mul_lt_mul_of_pos_right (show c - ε < c - ε / 2 by linarith) hscale
    linarith [hbound α hα hα0 hroot hd]
  · intro hc ε hε
    obtain ⟨D, hD, hbound⟩ := hc ε hε
    exact ⟨D, hD, fun α hα hα0 hroot hd => (hbound α hα hα0 hroot hd).le⟩

/-- The zero coefficient gives a lower bound independently of literature. -/
theorem asymptoticDobrowolskiConstant_nonneg : 0 ≤ asymptoticDobrowolskiConstant :=
  coe_le_asymptoticDobrowolskiConstant zero_isAsymptoticDobrowolskiCoefficient

/-- The catalogue's infinite upper row is just the top bound, not a finite estimate. -/
theorem asymptoticDobrowolskiConstant_le_top : asymptoticDobrowolskiConstant ≤ ⊤ :=
  le_top

end MathlibExt.NumberTheory.AsymptoticDobrowolski

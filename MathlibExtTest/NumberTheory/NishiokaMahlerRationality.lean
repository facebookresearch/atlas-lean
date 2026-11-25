/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.WellKnown
public import MathlibExt.NumberTheory.NishiokaMahlerRationality

open scoped Polynomial PowerSeries

namespace MathlibExtTest.NumberTheory.NishiokaMahlerRationality

open MetaMathlibExt

-- The order-zero Mahler relation is allowed and has the zero series as its only solution.
example : ∃ p q : ℂ[X], q ≠ 0 ∧ q.toPowerSeries * (0 : ℂ⟦X⟧) = p.toPowerSeries := by
  refine nishioka_algebraic_kMahler_is_rational 2 0 ?_ ?_
  · refine ⟨le_rfl, 0, fun _ => 1, by simp, by simp, ?_⟩
    have h : mahlerSubst (0 : ℂ⟦X⟧) 2 0 = 0 := by
      ext n
      simp [mahlerSubst, PowerSeries.coeff_mk]
    simp [h]
  · exact ⟨Polynomial.X, Polynomial.X_ne_zero, by simp⟩

-- The geometric series has infinite support and an order-one Mahler relation.
example :
    ∃ p q : ℂ[X], q ≠ 0 ∧
      q.toPowerSeries * (PowerSeries.mk 1 : ℂ⟦X⟧) = p.toPowerSeries := by
  let F : ℂ⟦X⟧ := PowerSeries.mk 1
  have hF : F * (1 - PowerSeries.X) = 1 :=
    PowerSeries.mk_one_mul_one_sub_eq_one ℂ
  refine nishioka_algebraic_kMahler_is_rational 2 F ?_ ?_
  · let a : Fin 2 → ℂ[X] := ![1 - Polynomial.X, Polynomial.X ^ 2 - 1]
    have ha₀ : a 0 ≠ 0 := by
      intro h
      have hc := congrArg (fun p : ℂ[X] => p.coeff 0) h
      simp [a] at hc
    have ha₁ : a 1 ≠ 0 := by
      intro h
      have hc := congrArg (fun p : ℂ[X] => p.coeff 0) h
      simp [a, Polynomial.coeff_X_pow] at hc
    have h₀ : mahlerSubst F 2 0 = F := by
      ext n
      simp [mahlerSubst]
    have h₁ : mahlerSubst F 2 1 = PowerSeries.expand 2 (by decide) F := by
      ext n
      simp [mahlerSubst, PowerSeries.coeff_expand]
    have hF₂ : PowerSeries.expand 2 (by decide) F * (1 - PowerSeries.X ^ 2) = 1 := by
      let e := PowerSeries.expand 2 (by decide) (R := ℂ)
      have h := congrArg e hF
      change e (F * (1 - PowerSeries.X)) = e 1 at h
      rw [map_mul, map_sub, map_one, show e PowerSeries.X = PowerSeries.X ^ 2 from
        PowerSeries.expand_X _ _] at h
      exact h
    refine ⟨le_rfl, 1, a, ha₀, ha₁, ?_⟩
    rw [Fin.sum_univ_two]
    change ((1 - Polynomial.X : ℂ[X]) : ℂ⟦X⟧) * mahlerSubst F 2 0 +
      ((Polynomial.X ^ 2 - 1 : ℂ[X]) : ℂ⟦X⟧) * mahlerSubst F 2 1 = 0
    rw [h₀, h₁]
    push_cast
    rw [mul_comm _ F, hF, ← neg_sub (1 : ℂ⟦X⟧), neg_mul, mul_comm _ (PowerSeries.expand _ _ F),
      hF₂, add_neg_cancel]
  · let q : ℂ[X] := 1 - Polynomial.X
    let P : ℂ[X][X] := Polynomial.C q * Polynomial.X - 1
    refine ⟨P, ?_, ?_⟩
    · intro h
      have hc := congrArg (fun p : ℂ[X][X] => p.coeff 0) h
      simp [P] at hc
    · have hq : algebraMap ℂ[X] ℂ⟦X⟧ q = 1 - PowerSeries.X := by
        rw [PowerSeries.algebraMap_apply']
        change PowerSeries.map (RingHom.id ℂ) (q : ℂ⟦X⟧) = _
        rw [PowerSeries.map_id, id_eq]
        simp [q]
      simp only [P, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_X, Polynomial.eval₂_one, hq, mul_comm _ F, hF, sub_self]

end MathlibExtTest.NumberTheory.NishiokaMahlerRationality

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.LinearRecurrence
import Mathlib.Algebra.Field.ZMod

/-!
# Distinct-root recurrence consumers and repeated-root counterexamples

All acceptance checks are named private declarations, so their proof terms remain available to
full/private trust audits and kernel replay. Concrete solutions are specified by initial values
or directly, not by assuming the closed form under test.
-/

namespace MathlibExtTest.LinearRecurrenceClosedForm

/-- Check a proposed coefficient vector on the initial window, then use the public theorem's
uniqueness clause to characterize every coefficient vector. -/
private theorem coefficients_iff_of_initial {K : Type*} [Field K] (E : LinearRecurrence K)
    {r : Fin E.order → K} (hr : Function.Injective r) (hroot : ∀ i, E.charPoly.IsRoot (r i))
    {u : ℕ → K} (hu : E.IsSolution u) (c₀ : Fin E.order → K)
    (hinit : ∀ j : Fin E.order, u j = ∑ i, c₀ i * r i ^ (j : ℕ)) (c : Fin E.order → K) :
    (∀ n, u n = ∑ i, c i * r i ^ n) ↔ c = c₀ := by
  have hs : E.IsSolution (fun n ↦ ∑ i, c₀ i * r i ^ n) :=
    E.isSolution_sum_mul_pow Finset.univ c₀ r (fun i _ ↦ hroot i)
  have hc₀ : ∀ n, u n = ∑ i, c₀ i * r i ^ n := by
    have heq : u = (fun n ↦ ∑ i, c₀ i * r i ^ n) := by
      apply (E.eq_iff_eqOn_range_order _ _ hu hs).2
      intro n hn
      exact hinit ⟨n, Finset.mem_range.mp hn⟩
    exact fun n ↦ congrFun heq n
  obtain ⟨d, _, hd⟩ := E.exists_unique_eq_sum_pow_of_injective hr hroot hu
  constructor
  · intro hc
    exact (hd c hc).trans (hd c₀ hc₀).symm
  · rintro rfl
    exact hc₀

private abbrev cubic : LinearRecurrence ℚ := ⟨3, ![6, -11, 6]⟩

private theorem cubic_roots :
    ∀ i : Fin 3, cubic.charPoly.IsRoot ((![1, 2, 3] : Fin 3 → ℚ) i) := by
  intro i
  fin_cases i <;>
    norm_num [cubic, LinearRecurrence.charPoly, Polynomial.IsRoot.def, Fin.sum_univ_succ]

private theorem cubic_coefficients (c : Fin 3 → ℚ) :
    (∀ n, cubic.mkSol ![0, 1, 5] n = ∑ i, c i * (![1, 2, 3] : Fin 3 → ℚ) i ^ n) ↔
      c = ![0, -1, 1] := by
  refine coefficients_iff_of_initial cubic (r := ![1, 2, 3]) (by decide) cubic_roots
    (cubic.is_sol_mkSol ![0, 1, 5]) ![0, -1, 1] ?_ c
  intro j
  rw [cubic.mkSol_eq_init]
  fin_cases j <;> norm_num [Fin.sum_univ_succ]

private theorem cubic_closed_form (n : ℕ) :
    cubic.mkSol ![0, 1, 5] n = (3 : ℚ) ^ n - 2 ^ n := by
  simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_comm] using
    (cubic_coefficients ![0, -1, 1]).2 rfl n

private abbrev zeroRoot : LinearRecurrence ℚ := ⟨2, ![0, 1]⟩

private theorem zeroRoot_roots :
    ∀ i : Fin 2, zeroRoot.charPoly.IsRoot ((![0, 1] : Fin 2 → ℚ) i) := by
  intro i
  fin_cases i <;>
    norm_num [zeroRoot, LinearRecurrence.charPoly, Polynomial.IsRoot.def, Fin.sum_univ_succ]

private theorem zeroRoot_solution :
    zeroRoot.IsSolution (fun n ↦ if n = 0 then 5 else 2) := by
  intro n
  simp [zeroRoot, Fin.sum_univ_succ]

private theorem zeroRoot_coefficients (c : Fin 2 → ℚ) :
    (∀ n, (if n = 0 then 5 else 2 : ℚ) = ∑ i, c i * (![0, 1] : Fin 2 → ℚ) i ^ n) ↔
      c = ![3, 2] := by
  refine coefficients_iff_of_initial zeroRoot (r := ![0, 1]) (by decide) zeroRoot_roots
    zeroRoot_solution ![3, 2] ?_ c
  intro j
  fin_cases j <;> norm_num [Fin.sum_univ_succ]

private abbrev finiteField : LinearRecurrence (ZMod 5) := ⟨2, ![4, 0]⟩

private theorem finiteField_roots :
    ∀ i : Fin 2, finiteField.charPoly.IsRoot ((![2, 3] : Fin 2 → ZMod 5) i) := by
  intro i
  fin_cases i <;>
    norm_num [finiteField, LinearRecurrence.charPoly, Polynomial.IsRoot.def, Fin.sum_univ_succ]
  decide

private theorem finiteField_coefficients (c : Fin 2 → ZMod 5) :
    (∀ n, finiteField.mkSol ![1, 0] n = ∑ i, c i * (![2, 3] : Fin 2 → ZMod 5) i ^ n) ↔
      c = ![3, 3] := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hr : Function.Injective (![2, 3] : Fin 2 → ZMod 5) := by decide
  refine coefficients_iff_of_initial (K := ZMod 5) finiteField (r := ![2, 3]) hr
    finiteField_roots (finiteField.is_sol_mkSol ![1, 0]) ![3, 3] ?_ c
  intro j
  rw [finiteField.mkSol_eq_init]
  revert j
  decide

private abbrev orderZero (K : Type*) [Field K] : LinearRecurrence K := ⟨0, ![]⟩

private theorem orderZero_closed_form {K : Type*} [Field K] {u : ℕ → K}
    (hu : (orderZero K).IsSolution u) :
    (∀ n, u n = 0) ∧
      (∃! c : Fin 0 → K, ∀ n, u n = ∑ i, c i * (Fin.elim0 i : K) ^ n) := by
  have h := (orderZero K).exists_unique_eq_sum_pow_of_injective (r := Fin.elim0)
    (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i) hu
  refine ⟨?_, h⟩
  obtain ⟨c, hc, _⟩ := h
  intro n
  simpa using hc n

private abbrev repeatedOne : LinearRecurrence ℚ := ⟨2, ![-1, 2]⟩

private theorem repeatedOne_roots :
    ∀ i : Fin 2, repeatedOne.charPoly.IsRoot ((![1, 1] : Fin 2 → ℚ) i) := by
  intro i
  fin_cases i <;>
    norm_num [repeatedOne, LinearRecurrence.charPoly, Polynomial.IsRoot.def, Fin.sum_univ_succ]

private theorem repeatedOne_solution : repeatedOne.IsSolution (fun n ↦ (n : ℚ)) := by
  intro n
  simp [repeatedOne, Fin.sum_univ_succ, Nat.cast_add]
  ring

private theorem repeatedOne_no_geometric_expansion :
    ¬ ∃ c : Fin 2 → ℚ, ∀ n : ℕ, (n : ℚ) = ∑ i, c i * (![1, 1] : Fin 2 → ℚ) i ^ n := by
  rintro ⟨c, hc⟩
  have h0 := hc 0
  have h1 := hc 1
  simp [Fin.sum_univ_succ] at h0 h1
  exact zero_ne_one (h0.trans h1.symm)

private abbrev repeatedZero : LinearRecurrence ℚ := ⟨2, ![0, 0]⟩

private theorem repeatedZero_roots :
    ∀ i : Fin 2, repeatedZero.charPoly.IsRoot ((![0, 0] : Fin 2 → ℚ) i) := by
  intro i
  fin_cases i <;>
    norm_num [repeatedZero, LinearRecurrence.charPoly, Polynomial.IsRoot.def, Fin.sum_univ_succ]

private theorem repeatedZero_solution :
    repeatedZero.IsSolution (fun n ↦ if n = 1 then 1 else 0) := by
  intro n
  have hn : n + 2 ≠ 1 := by omega
  simp [repeatedZero, Fin.sum_univ_succ, hn]

private theorem repeatedZero_no_geometric_expansion :
    ¬ ∃ c : Fin 2 → ℚ, ∀ n, (if n = 1 then 1 else 0 : ℚ) =
      ∑ i, c i * (![0, 0] : Fin 2 → ℚ) i ^ n := by
  rintro ⟨c, hc⟩
  have h1 := hc 1
  norm_num [Fin.sum_univ_succ] at h1

end MathlibExtTest.LinearRecurrenceClosedForm

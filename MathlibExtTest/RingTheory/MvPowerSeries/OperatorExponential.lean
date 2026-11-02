/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.MvPowerSeries.OperatorExponential
import Mathlib.Algebra.Polynomial.Derivation

/-! # Populated clients for formal coefficient-operator exponentials -/

open MvPowerSeries

section SourceAndLaws

variable {σ A : Type*} [CommRing A] [Algebra ℚ A]

example (O : σ → A →ₗ[ℚ] A) (N : ℕ) (f : MvPowerSeries σ A) :
    expOperatorPartial O N f =
      ∑ n ∈ Finset.range N, (n.factorial : ℚ)⁻¹ • (coefficientOperator O)^[n] f :=
  expOperatorPartial_apply O N f

-- Equality to the exact original coefficient constructor, including its iteration cutoff.
example (O : σ → A →ₗ[ℚ] A) (f : MvPowerSeries σ A) :
    expOperator O f = fun d => coeff d
      (∑ n ∈ Finset.range (d.degree + 1),
        (n.factorial : ℚ)⁻¹ • (coefficientOperator O)^[n] f) := by
  ext d
  rw [coeff_expOperator_def, expOperatorPartial_apply]
  rfl

example (O : σ → A →ₗ[ℚ] A) (f : MvPowerSeries σ A) :
    expOperatorPartial O 0 f = 0 := by
  simp [expOperatorPartial_apply]

example (O : σ → A →ₗ[ℚ] A) (f : MvPowerSeries σ A) :
    expOperatorPartial O 1 f = f := by
  simp [expOperatorPartial_apply]

-- The source's rational coefficient-scalar bridge is the canonical coefficient action.
example (q : ℚ) (f : MvPowerSeries σ A) (d : σ →₀ ℕ) :
    coeff d (q • f) = q • coeff d f := rfl

example (O : σ → A →ₗ[ℚ] A) (N : ℕ) (f g : MvPowerSeries σ A) (q : ℚ) :
    expOperatorPartial O N (q • f + g) =
      q • expOperatorPartial O N f + expOperatorPartial O N g := by
  rw [map_add, map_smul]

example (O : σ → A →ₗ[ℚ] A) (f g : MvPowerSeries σ A) (q : ℚ) :
    expOperator O (q • f + g) = q • expOperator O f + expOperator O g := by
  rw [map_add, map_smul]

example (O : σ → A →ₗ[ℚ] A) (N : ℕ) : expOperatorPartial O N 0 = 0 := map_zero _

example (O : σ → A →ₗ[ℚ] A) : expOperator O 0 = 0 := map_zero _

example (O : σ → A →ₗ[ℚ] A) (f : MvPowerSeries σ A) (d : σ →₀ ℕ) :
    coeff d (expOperator O f) = coeff d (expOperatorPartial O (d.degree + 1) f) :=
  coeff_expOperator_def O f d

example (O : σ → A →ₗ[ℚ] A) (f : MvPowerSeries σ A) (d : σ →₀ ℕ) :
    coeff d (expOperator O f) = coeff d (expOperatorPartial O (d.degree + 5) f) :=
  coeff_expOperator O f (by omega)

example (O : σ → A →ₗ[ℚ] A) (f : MvPowerSeries σ A) :
    constantCoeff (expOperator O f) = constantCoeff f := constantCoeff_expOperator O f

example (f : MvPowerSeries σ A) :
    expOperator (fun _ => (0 : A →ₗ[ℚ] A)) f = f := by
  rw [expOperator_zero_family]
  rfl

example (O : σ → A →ₗ[ℚ] A) {f : MvPowerSeries σ A}
    (hf : coefficientOperator O (coefficientOperator O f) = 0) :
    expOperator O f = f + coefficientOperator O f := expOperator_of_sq_zero O hf

example (O : σ → A →ₗ[ℚ] A) {f : MvPowerSeries σ A}
    (hf : coefficientOperator O f = 0) : expOperator O f = f := expOperator_of_zero O hf

example (O : Empty → A →ₗ[ℚ] A) : expOperator O = LinearMap.id := by
  ext f d
  have hf : coefficientOperator O f = 0 := by
    ext e
    have he : e = 0 := by
      ext i
      exact isEmptyElim i
    subst e
    simp
  rw [expOperator_of_zero _ hf]
  rfl

end SourceAndLaws

private theorem coeff_iterate_constant_single {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (O : σ → A →ₗ[ℚ] A) (a : A) (m n : ℕ) (i : σ) :
    coeff (Finsupp.single i n) ((coefficientOperator O)^[m] (C a)) =
      if n = m then (O i)^[m] a else 0 := by
  classical
  induction m generalizing n with
  | zero => simp [coeff_C]
  | succ m ih =>
    cases n with
    | zero => simp [Function.iterate_succ_apply']
    | succ n =>
      rw [Function.iterate_succ_apply', coeff_coefficientOperator,
        Finsupp.support_single _ (by omega)]
      simp only [Finset.sum_singleton, ← Finsupp.single_tsub, Nat.add_sub_cancel,
        ih, Nat.succ.injEq, Function.iterate_succ_apply']
      split_ifs <;> simp

private theorem coeff_identity_exp (n : ℕ) (i : Fin 2) :
    coeff (Finsupp.single i n)
      (expOperator (fun _ : Fin 2 => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) (C 2)) =
      (n.factorial : ℚ)⁻¹ * 2 := by
  classical
  rw [coeff_expOperator_def, Finsupp.degree_single, expOperatorPartial_apply, map_sum]
  change (∑ m ∈ Finset.range (n + 1),
    (m.factorial : ℚ)⁻¹ • coeff (Finsupp.single i n)
      ((coefficientOperator (fun _ : Fin 2 => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)))^[m] (C 2))) = _
  simp [coeff_iterate_constant_single, smul_eq_mul]

private theorem coeff_exp_constant_single {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (O : σ → A →ₗ[ℚ] A) (a : A) (n : ℕ) (i : σ) :
    coeff (Finsupp.single i n) (expOperator O (C a)) =
      (n.factorial : ℚ)⁻¹ • (O i)^[n] a := by
  classical
  rw [coeff_expOperator_def, Finsupp.degree_single, expOperatorPartial_apply, map_sum]
  change (∑ m ∈ Finset.range (n + 1),
    (m.factorial : ℚ)⁻¹ • coeff (Finsupp.single i n)
      ((coefficientOperator O)^[m] (C a))) = _
  simp [coeff_iterate_constant_single]

example (n : ℕ) (i : Fin 2) :
    coeff (Finsupp.single i n)
      (expOperator (fun _ : Fin 2 => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) (C 2)) =
      2 / (n.factorial : ℚ) := by
  rw [coeff_identity_exp]
  ring

example (i : Fin 2) :
    coeff (Finsupp.single i 0)
      (expOperator (fun _ : Fin 2 => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) (C 2)) = 2 := by
  rw [coeff_identity_exp]
  norm_num

example (i : Fin 2) :
    coeff (Finsupp.single i 1)
      (expOperator (fun _ : Fin 2 => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) (C 2)) = 2 := by
  rw [coeff_identity_exp]
  norm_num

example (i : Fin 2) :
    coeff (Finsupp.single i 2)
      (expOperator (fun _ : Fin 2 => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) (C 2)) = 1 := by
  rw [coeff_identity_exp]
  norm_num

example (i : Fin 2) :
    coeff (Finsupp.single i 3)
      (expOperator (fun _ : Fin 2 => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) (C 2)) = 1 / 3 := by
  rw [coeff_identity_exp]
  norm_num [Nat.factorial]

example (i : ℕ) : coeff (Finsupp.single i 1)
    (expOperator (fun j : ℕ => (j + 1 : ℚ) • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) (C 1)) =
      (i + 1 : ℚ) := by
  rw [coeff_exp_constant_single]
  simp

private noncomputable def scaledOperators (i : Fin 2) : ℚ →ₗ[ℚ] ℚ :=
  if i = 0 then LinearMap.id else 2 • LinearMap.id

private theorem sub_first (n m : ℕ) :
    (Finsupp.single (0 : Fin 2) (n + 1) + Finsupp.single 1 m) - Finsupp.single 0 1 =
      Finsupp.single 0 n + Finsupp.single 1 m := by
  ext i
  fin_cases i <;> simp

private theorem sub_second (n m : ℕ) :
    (Finsupp.single (0 : Fin 2) n + Finsupp.single 1 (m + 1)) - Finsupp.single 1 1 =
      Finsupp.single 0 n + Finsupp.single 1 m := by
  ext i
  fin_cases i <;> simp

example : coeff (Finsupp.single (0 : Fin 2) 2 + Finsupp.single 1 1)
    (expOperator scaledOperators (C 1)) = 1 := by
  classical
  rw [coeff_expOperator_def, expOperatorPartial_apply]
  norm_num [Function.iterate_succ_apply', coeff_coefficientOperator, scaledOperators,
    Finset.sum_range_succ, Finsupp.support_add_eq_union, sub_first, sub_second,
    ← Finsupp.single_tsub, coeff_C, coeff_one, Nat.factorial]

private theorem polynomial_derivative_high (n : ℕ) (hn : 3 ≤ n) :
    ((Polynomial.derivative' (R := ℚ)).toLinearMap)^[n] (Polynomial.X ^ 2) = 0 := by
  rw [← Module.End.coe_pow]
  apply Module.End.pow_map_zero_of_le (k := 3) hn
  norm_num [Module.End.coe_pow, Function.iterate_succ_apply', Polynomial.derivative'_apply,
    Polynomial.C_ofNat]

-- A real coefficient derivation gives the complete finite Taylor expansion.
example : expOperator
    (fun _ : Unit => (Polynomial.derivative' (R := ℚ)).toLinearMap)
    (C (Polynomial.X ^ 2)) =
      C (Polynomial.X ^ 2) + monomial (Finsupp.single () 1) (2 * Polynomial.X) +
        monomial (Finsupp.single () 2) (1 : Polynomial ℚ) := by
  classical
  apply MvPowerSeries.ext
  intro d
  have hd : d = Finsupp.single () (d ()) := by
    apply Finsupp.ext
    intro i
    cases i
    simp
  rw [hd, coeff_exp_constant_single]
  simp only [map_add, coeff_monomial, coeff_C]
  generalize d () = n
  rcases n with _ | n
  · simp [eq_comm]
  rcases n with _ | n
  · norm_num [Polynomial.derivative'_apply, Polynomial.C_ofNat, coeff_monomial]
  rcases n with _ | n
  · norm_num [Function.iterate_succ_apply', Polynomial.derivative'_apply,
      Polynomial.C_ofNat, Algebra.smul_def]
    change Polynomial.C (1 / 2 : ℚ) * Polynomial.C 2 = Polynomial.C 1
    rw [← map_mul]
    norm_num
  · rw [polynomial_derivative_high _ (by omega), smul_zero]
    simp only [Finsupp.single_eq_zero, Nat.succ_ne_zero, ↓reduceIte]
    have h : Finsupp.single () (n + 1 + 1 + 1) ≠ Finsupp.single () 2 := by
      intro he
      have := congrArg (fun e : Unit →₀ ℕ => e ()) he
      simp only [Finsupp.single_eq_same] at this
      omega
    simp only [h, ↓reduceIte, add_zero]
    split_ifs with he
    · have := congrArg (fun e : Unit →₀ ℕ => e ()) he
      simp only [Finsupp.single_eq_same] at this
      omega
    · simp

example : expOperator
    (fun _ : Unit => (Polynomial.derivative' (R := ℚ)).toLinearMap)
    (C Polynomial.X) = C Polynomial.X + coefficientOperator
      (fun _ : Unit => (Polynomial.derivative' (R := ℚ)).toLinearMap) (C Polynomial.X) := by
  apply expOperator_of_sq_zero
  apply MvPowerSeries.ext
  intro d
  have hd : d = Finsupp.single () (d ()) := by
    apply Finsupp.ext
    intro i
    cases i
    simp
  rw [hd]
  change coeff (Finsupp.single () (d ()))
    ((coefficientOperator (fun _ : Unit =>
      (Polynomial.derivative' (R := ℚ)).toLinearMap))^[2] (C Polynomial.X)) = 0
  rw [coeff_iterate_constant_single]
  simp [Function.iterate_succ_apply', Polynomial.derivative'_apply]

private noncomputable def noncommutingDerivations (i : Fin 2) :
    Derivation ℚ (Polynomial ℚ) (Polynomial ℚ) :=
  if i = 0 then Polynomial.derivative' else
    (Polynomial.X : Polynomial ℚ) • (Polynomial.derivative' (R := ℚ))

example : noncommutingDerivations 0 (noncommutingDerivations 1 Polynomial.X) = 1 := by
  simp [noncommutingDerivations, Derivation.smul_apply, Polynomial.derivative'_apply,
    smul_eq_mul]

example : noncommutingDerivations 1 (noncommutingDerivations 0 Polynomial.X) = 0 := by
  simp [noncommutingDerivations, Polynomial.derivative'_apply]

-- The mixed coefficient includes both orders of the noncommuting operators.
example : coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)
    (expOperator (fun i => (noncommutingDerivations i).toLinearMap)
      (C (Polynomial.X ^ 2))) = 3 * (Polynomial.X : Polynomial ℚ) := by
  classical
  rw [coeff_expOperator_def, expOperatorPartial_apply]
  norm_num [Function.iterate_succ_apply', coeff_coefficientOperator,
    noncommutingDerivations, Derivation.smul_apply, Polynomial.derivative'_apply,
    Polynomial.C_ofNat, smul_eq_mul, Finset.sum_range_succ, Finsupp.support_add_eq_union,
    sub_first, sub_second, ← Finsupp.single_tsub, coeff_C, Nat.factorial]
  simp only [← map_pow, coeff_C]
  norm_num [Algebra.smul_def]
  ring_nf
  norm_num [← Polynomial.C_ofNat, ← map_mul]
  have hscale : Polynomial.C (1 / 2 : ℚ) * 6 = 3 := by
    change Polynomial.C (1 / 2 : ℚ) * Polynomial.C 6 = Polynomial.C 3
    rw [← map_mul]
    norm_num
  rw [mul_right_comm (Polynomial.C (1 / 2 : ℚ)) Polynomial.X 6, hscale]
  ring

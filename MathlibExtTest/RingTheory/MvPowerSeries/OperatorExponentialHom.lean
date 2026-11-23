/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.MvPowerSeries.OperatorExponentialHom
public import Mathlib.Algebra.Polynomial.Derivation

/-! # Clients for the operator exponential ring homomorphism -/

@[expose] public section

open MvPowerSeries

section GenericClients

variable {σ A : Type*} [CommRing A] [Algebra ℚ A]

private noncomputable def sourceDerivations (O : σ → A →ₗ[ℚ] A)
    (hO : ∀ i a b, O i (a * b) = a * O i b + O i a * b)
    (i : σ) : Derivation ℚ A A :=
  Derivation.mk' (O i) fun a b => by
    change O i (a * b) = a * O i b + b * O i a
    rw [hO i a b, mul_comm (O i a) b]

-- Exact source-style linear maps and local Leibniz hypotheses recover multiplicativity.
example (O : σ → A →ₗ[ℚ] A)
    (hO : ∀ i a b, O i (a * b) = a * O i b + O i a * b)
    (f g : MvPowerSeries σ A) :
    expOperator O (f * g) = expOperator O f * expOperator O g := by
  simpa only [sourceDerivations, Derivation.coe_mk'_linearMap] using
    expOperator_mul (sourceDerivations O hO) f g

example (O : σ → A →ₗ[ℚ] A)
    (hO : ∀ i a b, O i (a * b) = a * O i b + O i a * b) :
    expOperator O (1 : MvPowerSeries σ A) = 1 := by
  simpa only [sourceDerivations, Derivation.coe_mk'_linearMap] using
    expOperator_one (sourceDerivations O hO)

example (O : σ → A →ₗ[ℚ] A)
    (hO : ∀ i a b, O i (a * b) = a * O i b + O i a * b)
    (f : MvPowerSeries σ A) :
    expOperatorHom (sourceDerivations O hO) f = expOperator O f := by
  simp only [expOperatorHom_apply, sourceDerivations, Derivation.coe_mk'_linearMap]

example (O : σ → A →ₗ[ℚ] A)
    (hO : ∀ i a b, O i (a * b) = a * O i b + O i a * b)
    {w : MvPowerSeries σ A} (hw : constantCoeff w = 0) :
    expOperator O (expOfConstantCoeffZero w hw) =
      expOfConstantCoeffZero (expOperator O w)
        (by rw [constantCoeff_expOperator, hw]) := by
  simpa only [sourceDerivations, Derivation.coe_mk'_linearMap] using
    expOperator_expOfConstantCoeffZero (sourceDerivations O hO) hw

example (D : σ → Derivation ℚ A A) (f g : MvPowerSeries σ A) :
    expOperator (fun i => (D i).toLinearMap) (f * g) =
      expOperator (fun i => (D i).toLinearMap) f *
        expOperator (fun i => (D i).toLinearMap) g :=
  expOperator_mul D f g

example (D : σ → Derivation ℚ A A) :
    expOperator (fun i => (D i).toLinearMap) (1 : MvPowerSeries σ A) = 1 :=
  expOperator_one D

example (D : σ → Derivation ℚ A A) (f : MvPowerSeries σ A) :
    expOperatorHom D f = expOperator (fun i => (D i).toLinearMap) f := rfl

example (O : σ → A →ₗ[ℚ] A) (d : σ →₀ ℕ) (f g : MvPowerSeries σ A)
    (h : ∀ e : σ →₀ ℕ, e.degree ≤ d.degree → coeff e f = coeff e g) :
    coeff d (expOperator O f) = coeff d (expOperator O g) :=
  coeff_expOperator_congr O d f g h

example (D : σ → Derivation ℚ A A) {w : MvPowerSeries σ A}
    (hw : constantCoeff w = 0) :
    expOperator (fun i => (D i).toLinearMap) (expOfConstantCoeffZero w hw) =
      expOfConstantCoeffZero (expOperator (fun i => (D i).toLinearMap) w)
        (by rw [constantCoeff_expOperator, hw]) :=
  expOperator_expOfConstantCoeffZero D hw

-- The public API retains arbitrary, potentially infinite variable families.
example (D : ℕ → Derivation ℚ A A) (f g : MvPowerSeries ℕ A) :
    expOperatorHom D (f * g) = expOperatorHom D f * expOperatorHom D g :=
  map_mul (expOperatorHom D) f g

end GenericClients

section FiltrationAndBoundaries

variable {σ A : Type*} [CommRing A] [Algebra ℚ A]

-- Changing only a quadratic coefficient cannot change a chosen linear coefficient.
example (O : σ → A →ₗ[ℚ] A) (f : MvPowerSeries σ A) (i : σ) (a : A) :
    coeff (Finsupp.single i 1) (expOperator O f) =
      coeff (Finsupp.single i 1)
        (expOperator O (f + monomial (Finsupp.single i 2) a)) := by
  classical
  apply coeff_expOperator_congr
  intro e he
  rw [map_add, coeff_monomial]
  split_ifs with heq
  · subst e
    simp at he
  · simp

-- If low coefficients differ, the corresponding exponential coefficient can differ too.
example : coeff 0
      (expOperator (fun _ : Unit => (Polynomial.derivative' (R := ℚ)).toLinearMap)
        (0 : MvPowerSeries Unit (Polynomial ℚ))) ≠
    coeff 0
      (expOperator (fun _ : Unit => (Polynomial.derivative' (R := ℚ)).toLinearMap)
        (C (1 : Polynomial ℚ))) := by
  simp [coeff_zero_eq_constantCoeff_apply]

example (O : σ → A →ₗ[ℚ] A) (f : MvPowerSeries σ A) :
    expOperatorPartial O 0 f = 0 := by
  simp [expOperatorPartial_apply]

example (D : σ → Derivation ℚ A A) : expOperatorHom D 1 = 1 := map_one _

example (D : σ → Derivation ℚ A A) : expOperatorHom D 0 = 0 := map_zero _

example (f : MvPowerSeries σ A) :
    expOperatorHom (fun _ : σ => (0 : Derivation ℚ A A)) f = f := by
  change expOperator (fun _ : σ => (0 : A →ₗ[ℚ] A)) f = f
  rw [expOperator_zero_family]
  rfl

end FiltrationAndBoundaries

private noncomputable def polynomialDerivations (_ : Unit) :
    Derivation ℚ (Polynomial ℚ) (Polynomial ℚ) :=
  Polynomial.derivative'

private noncomputable def nonlinearSeries : MvPowerSeries Unit (Polynomial ℚ) :=
  X () + X () ^ 2

private theorem nonlinearSeries_constantCoeff : constantCoeff nonlinearSeries = 0 := by
  simp [nonlinearSeries]

private noncomputable def coefficientChangingSeries :
    MvPowerSeries Unit (Polynomial ℚ) :=
  monomial (Finsupp.single () 1) Polynomial.X +
    monomial (Finsupp.single () 2) (Polynomial.X ^ 2)

private theorem coeff_coefficientChangingSeries (n : ℕ) :
    coeff (Finsupp.single () n) coefficientChangingSeries =
      if n = 1 then Polynomial.X else if n = 2 then Polynomial.X ^ 2 else 0 := by
  classical
  rw [coefficientChangingSeries, map_add, coeff_monomial, coeff_monomial]
  by_cases h1 : n = 1 <;> by_cases h2 : n = 2 <;> simp [h1, h2]

private theorem coefficientChangingSeries_constantCoeff :
    constantCoeff coefficientChangingSeries = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  rw [show (0 : Unit →₀ ℕ) = Finsupp.single () 0 by simp,
    coeff_coefficientChangingSeries]
  simp

private theorem coeff_iterate_unit_coefficientOperator
    (O : Polynomial ℚ →ₗ[ℚ] Polynomial ℚ) (f : MvPowerSeries Unit (Polynomial ℚ))
    (m n : ℕ) :
    coeff (Finsupp.single () n) ((coefficientOperator fun _ : Unit => O)^[m] f) =
      if m ≤ n then O^[m] (coeff (Finsupp.single () (n - m)) f) else 0 := by
  classical
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
    cases n with
    | zero => simp [Function.iterate_succ_apply']
    | succ n =>
      rw [Function.iterate_succ_apply', coeff_coefficientOperator,
        Finsupp.support_single _ (by omega)]
      simp only [Finset.sum_singleton, ← Finsupp.single_tsub, ih,
        Nat.succ_le_succ_iff, Nat.succ_sub_succ_eq_sub, Function.iterate_succ_apply']
      by_cases hmn : m ≤ n <;> simp [hmn]

-- This nonlinear input follows the coefficient-changing, rather than identity, operator path.
example : coeff (Finsupp.single () 2)
    (expOperator (fun _ : Unit => (Polynomial.derivative' (R := ℚ)).toLinearMap)
      coefficientChangingSeries) = Polynomial.X ^ 2 + 1 := by
  rw [coeff_expOperator_def, Finsupp.degree_single, expOperatorPartial_apply, map_sum]
  change (∑ m ∈ Finset.range 3, (m.factorial : ℚ)⁻¹ •
    coeff (Finsupp.single () 2)
      ((coefficientOperator fun _ : Unit =>
        (Polynomial.derivative' (R := ℚ)).toLinearMap)^[m]
          coefficientChangingSeries)) = _
  simp_rw [coeff_iterate_unit_coefficientOperator]
  norm_num [Finset.sum_range_succ, ← Finsupp.single_tsub]
  have h2 : (PowerSeries.coeff 2) coefficientChangingSeries = Polynomial.X ^ 2 := by
    simpa using coeff_coefficientChangingSeries 2
  have h1 : (PowerSeries.coeff 1) coefficientChangingSeries = Polynomial.X := by
    simpa using coeff_coefficientChangingSeries 1
  have h0 : PowerSeries.constantCoeff coefficientChangingSeries = 0 :=
    coefficientChangingSeries_constantCoeff
  rw [h2, h1, h0]
  norm_num [
    Function.iterate_succ_apply', Polynomial.derivative'_apply, Polynomial.C_ofNat,
    Nat.factorial]

example : expOperatorHom polynomialDerivations (expTrunc 3 coefficientChangingSeries) =
    expTrunc 3 (expOperatorHom polynomialDerivations coefficientChangingSeries) :=
  map_expTrunc (expOperatorHom polynomialDerivations) 3 coefficientChangingSeries

example : expOperatorHom polynomialDerivations
      (expOfConstantCoeffZero coefficientChangingSeries
        coefficientChangingSeries_constantCoeff) =
    expOfConstantCoeffZero
      (expOperatorHom polynomialDerivations coefficientChangingSeries)
      (by rw [expOperatorHom_apply, constantCoeff_expOperator,
        coefficientChangingSeries_constantCoeff]) :=
  expOperator_expOfConstantCoeffZero polynomialDerivations
    coefficientChangingSeries_constantCoeff

private theorem coeff_exp_coefficientChangingSeries_one :
    coeff (Finsupp.single () 1)
      (expOfConstantCoeffZero coefficientChangingSeries
        coefficientChangingSeries_constantCoeff) = Polynomial.X := by
  rw [coeff_expOfConstantCoeffZero_degree, Finsupp.degree_single]
  have htrunc : expTrunc 2 coefficientChangingSeries = 1 + coefficientChangingSeries := by
    norm_num [expTrunc, Finset.sum_range_succ]
  rw [htrunc, map_add, coeff_coefficientChangingSeries]
  simp [coeff_one]

private theorem coeff_coefficientChangingSeries_sq_two :
    coeff (Finsupp.single () 2) (coefficientChangingSeries ^ 2) =
      Polynomial.X ^ 2 := by
  classical
  rw [pow_two, coefficientChangingSeries]
  simp only [add_mul, mul_add, map_add, monomial_mul_monomial]
  simp [coeff_monomial]
  have h11 : Finsupp.single () 2 =
      Finsupp.single () 1 + Finsupp.single () 1 := by
    ext
    simp
  rw [h11]
  simp
  ring

private theorem coeff_exp_coefficientChangingSeries_two :
    coeff (Finsupp.single () 2)
      (expOfConstantCoeffZero coefficientChangingSeries
        coefficientChangingSeries_constantCoeff) =
      (3 / 2 : ℚ) • Polynomial.X ^ 2 := by
  rw [coeff_expOfConstantCoeffZero_degree, Finsupp.degree_single]
  have htrunc : expTrunc 3 coefficientChangingSeries =
      1 + coefficientChangingSeries + (1 / 2 : ℚ) • coefficientChangingSeries ^ 2 := by
    norm_num [expTrunc, Finset.sum_range_succ, Nat.factorial]
  rw [htrunc, map_add, map_add, map_rat_smul, coeff_coefficientChangingSeries,
    coeff_coefficientChangingSeries_sq_two]
  norm_num [coeff_one, Polynomial.qsmul_eq_C_mul]
  have hrat : Polynomial.C (3 / 2 : ℚ) =
      1 + Polynomial.C (1 / 2 : ℚ) := by
    rw [show (3 / 2 : ℚ) = 1 + 1 / 2 by norm_num, map_add, map_one]
  rw [hrat]
  ring

private theorem coeff_exp_coefficientChangingSeries_zero :
    coeff (Finsupp.single () 0)
      (expOfConstantCoeffZero coefficientChangingSeries
        coefficientChangingSeries_constantCoeff) = 1 := by
  rw [show Finsupp.single () 0 = (0 : Unit →₀ ℕ) by simp,
    coeff_zero_eq_constantCoeff_apply, constantCoeff_expOfConstantCoeffZero]

-- The full compatibility path has a populated, coefficient-changing quadratic output.
example : coeff (Finsupp.single () 2)
    (expOperatorHom polynomialDerivations
      (expOfConstantCoeffZero coefficientChangingSeries
        coefficientChangingSeries_constantCoeff)) =
      (3 / 2 : ℚ) • Polynomial.X ^ 2 + 1 := by
  rw [expOperatorHom_apply, coeff_expOperator_def, Finsupp.degree_single,
    expOperatorPartial_apply, map_sum]
  change (∑ m ∈ Finset.range 3, (m.factorial : ℚ)⁻¹ •
    coeff (Finsupp.single () 2)
      ((coefficientOperator fun _ : Unit =>
        (Polynomial.derivative' (R := ℚ)).toLinearMap)^[m]
          (expOfConstantCoeffZero coefficientChangingSeries
            coefficientChangingSeries_constantCoeff))) = _
  simp_rw [coeff_iterate_unit_coefficientOperator]
  norm_num [Finset.sum_range_succ, ← Finsupp.single_tsub]
  have h2 : (PowerSeries.coeff 2)
      (expOfConstantCoeffZero coefficientChangingSeries
        coefficientChangingSeries_constantCoeff) =
      (3 / 2 : ℚ) • Polynomial.X ^ 2 := by
    simpa using coeff_exp_coefficientChangingSeries_two
  have h1 : (PowerSeries.coeff 1)
      (expOfConstantCoeffZero coefficientChangingSeries
        coefficientChangingSeries_constantCoeff) = Polynomial.X := by
    simpa using coeff_exp_coefficientChangingSeries_one
  have h0 : PowerSeries.constantCoeff
      (expOfConstantCoeffZero coefficientChangingSeries
        coefficientChangingSeries_constantCoeff) = 1 := by
    exact constantCoeff_expOfConstantCoeffZero coefficientChangingSeries
      coefficientChangingSeries_constantCoeff
  rw [h2, h1, h0]
  norm_num [Function.iterate_succ_apply',
    Polynomial.derivative'_apply, Polynomial.C_ofNat, Nat.factorial, Algebra.smul_def]

-- Finite compatibility is inherited from the canonical ring homomorphism, for arbitrary input.
example : expOperatorHom polynomialDerivations (expTrunc 4 nonlinearSeries) =
    expTrunc 4 (expOperatorHom polynomialDerivations nonlinearSeries) :=
  map_expTrunc (expOperatorHom polynomialDerivations) 4 nonlinearSeries

-- The full formal exponential uses the same nonlinear zero-constant input.
example : expOperatorHom polynomialDerivations
      (expOfConstantCoeffZero nonlinearSeries nonlinearSeries_constantCoeff) =
    expOfConstantCoeffZero (expOperatorHom polynomialDerivations nonlinearSeries)
      (by rw [expOperatorHom_apply, constantCoeff_expOperator,
        nonlinearSeries_constantCoeff]) :=
  expOperator_expOfConstantCoeffZero polynomialDerivations
    nonlinearSeries_constantCoeff

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

private theorem coeff_expOperator_C_single {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (O : σ → A →ₗ[ℚ] A) (a : A) (n : ℕ) (i : σ) :
    coeff (Finsupp.single i n) (expOperator O (C a)) =
      (n.factorial : ℚ)⁻¹ • (O i)^[n] a := by
  classical
  rw [coeff_expOperator_def, Finsupp.degree_single, expOperatorPartial_apply, map_sum]
  change (∑ m ∈ Finset.range (n + 1),
    (m.factorial : ℚ)⁻¹ • coeff (Finsupp.single i n)
      ((coefficientOperator O)^[m] (C a))) = _
  simp [coeff_iterate_constant_single]

-- The derivative exponential of `C (X²)` has populated coefficients `X²`, `2X`, and `1`.
example : coeff (0 : Unit →₀ ℕ)
    (expOperator (fun _ : Unit => (Polynomial.derivative' (R := ℚ)).toLinearMap)
      (C (Polynomial.X ^ 2))) = Polynomial.X ^ 2 := by
  rw [show (0 : Unit →₀ ℕ) = Finsupp.single () 0 by simp,
    coeff_expOperator_C_single]
  simp

example : coeff (Finsupp.single () 1)
    (expOperator (fun _ : Unit => (Polynomial.derivative' (R := ℚ)).toLinearMap)
      (C (Polynomial.X ^ 2))) = 2 * Polynomial.X := by
  rw [coeff_expOperator_C_single]
  norm_num [Polynomial.derivative'_apply, Polynomial.C_ofNat]

example : coeff (Finsupp.single () 2)
    (expOperator (fun _ : Unit => (Polynomial.derivative' (R := ℚ)).toLinearMap)
      (C (Polynomial.X ^ 2))) = (1 : Polynomial ℚ) := by
  rw [coeff_expOperator_C_single]
  norm_num [Function.iterate_succ_apply', Polynomial.derivative'_apply,
    Polynomial.C_ofNat, Algebra.smul_def]
  change Polynomial.C (1 / 2 : ℚ) * Polynomial.C 2 = Polynomial.C 1
  rw [← map_mul]
  norm_num

-- A nonzero constant survives in `C (X + 2)`, while the linear output is nonzero.
example : coeff (0 : Unit →₀ ℕ)
    (expOperator (fun _ : Unit => (Polynomial.derivative' (R := ℚ)).toLinearMap)
      (C (Polynomial.X + 2))) = Polynomial.X + 2 := by
  rw [show (0 : Unit →₀ ℕ) = Finsupp.single () 0 by simp,
    coeff_expOperator_C_single]
  simp

example : coeff (Finsupp.single () 1)
    (expOperator (fun _ : Unit => (Polynomial.derivative' (R := ℚ)).toLinearMap)
      (C (Polynomial.X + 2))) = (1 : Polynomial ℚ) := by
  rw [coeff_expOperator_C_single]
  norm_num [Polynomial.derivative'_apply, Polynomial.C_ofNat]

-- Multiplicativity computes the linear product coefficient as `(X²(X+2))'`.
example : coeff (Finsupp.single () 1)
    (expOperator (fun _ : Unit => (Polynomial.derivative' (R := ℚ)).toLinearMap)
        (C (Polynomial.X ^ 2)) *
      expOperator (fun _ : Unit => (Polynomial.derivative' (R := ℚ)).toLinearMap)
        (C (Polynomial.X + 2))) =
      3 * Polynomial.X ^ 2 + 4 * Polynomial.X := by
  rw [← expOperator_mul (fun _ : Unit => Polynomial.derivative'), ← map_mul,
    coeff_expOperator_C_single]
  norm_num [Polynomial.derivative'_apply, Polynomial.C_ofNat]
  ring

private noncomputable def noncommutingDerivations (i : Fin 2) :
    Derivation ℚ (Polynomial ℚ) (Polynomial ℚ) :=
  if i = 0 then Polynomial.derivative' else
    (Polynomial.X : Polynomial ℚ) • (Polynomial.derivative' (R := ℚ))

private theorem sub_first (n m : ℕ) :
    (Finsupp.single (0 : Fin 2) (n + 1) + Finsupp.single 1 m) -
        Finsupp.single 0 1 =
      Finsupp.single 0 n + Finsupp.single 1 m := by
  ext i
  fin_cases i <;> simp

private theorem sub_second (n m : ℕ) :
    (Finsupp.single (0 : Fin 2) n + Finsupp.single 1 (m + 1)) -
        Finsupp.single 1 1 =
      Finsupp.single 0 n + Finsupp.single 1 m := by
  ext i
  fin_cases i <;> simp

-- The two derivations genuinely do not commute.
example : noncommutingDerivations 0 (noncommutingDerivations 1 Polynomial.X) = 1 := by
  simp [noncommutingDerivations, Derivation.smul_apply, Polynomial.derivative'_apply,
    smul_eq_mul]

example : noncommutingDerivations 1 (noncommutingDerivations 0 Polynomial.X) = 0 := by
  simp [noncommutingDerivations, Polynomial.derivative'_apply]

-- Product preservation still holds for the noncommuting family.
example : expOperator (fun i => (noncommutingDerivations i).toLinearMap)
      (C Polynomial.X * C Polynomial.X) =
    expOperator (fun i => (noncommutingDerivations i).toLinearMap) (C Polynomial.X) *
      expOperator (fun i => (noncommutingDerivations i).toLinearMap) (C Polynomial.X) :=
  expOperator_mul noncommutingDerivations _ _

-- For `f = g = C X`, the mixed product coefficient is the nonzero value `3X`.
example : coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)
    (expOperator (fun i => (noncommutingDerivations i).toLinearMap) (C Polynomial.X) *
      expOperator (fun i => (noncommutingDerivations i).toLinearMap) (C Polynomial.X)) =
      3 * (Polynomial.X : Polynomial ℚ) := by
  rw [← expOperator_mul noncommutingDerivations, ← map_mul]
  rw [show (Polynomial.X : Polynomial ℚ) * Polynomial.X = Polynomial.X ^ 2 by ring]
  change coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)
    (expOperator (fun i => (noncommutingDerivations i).toLinearMap)
      (C (Polynomial.X ^ 2))) = 3 * Polynomial.X
  classical
  rw [coeff_expOperator_def, expOperatorPartial_apply]
  norm_num [Function.iterate_succ_apply', coeff_coefficientOperator,
    noncommutingDerivations, Derivation.smul_apply, Polynomial.derivative'_apply,
    Polynomial.C_ofNat, smul_eq_mul, Finset.sum_range_succ,
    Finsupp.support_add_eq_union, sub_first, sub_second, ← Finsupp.single_tsub,
    coeff_C, Nat.factorial]
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

-- Transitive trusted-axiom audit of every public declaration added in the source module.
#print axioms MvPowerSeries.expOperator_mul
#print axioms MvPowerSeries.expOperator_one
#print axioms MvPowerSeries.expOperatorHom
#print axioms MvPowerSeries.expOperatorHom_apply
#print axioms MvPowerSeries.coeff_expOperator_congr
#print axioms MvPowerSeries.expOperator_expOfConstantCoeffZero

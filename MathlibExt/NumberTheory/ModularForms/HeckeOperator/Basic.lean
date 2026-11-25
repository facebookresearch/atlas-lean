/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ModularForm_HeckeOperator.lean`,
`Theorems/Thm_ModularForm_coeffHeckeT_comm.lean`,
`P2M/Sol/S_ModularForm_coeffHeckeT_comm.lean`,
`Theorems/Thm_ModularForm_coeffHeckeU_comm.lean`,
`P2M/Sol/S_ModularForm_coeffHeckeU_comm.lean`,
`Theorems/Thm_ModularForm_coeffHeckeT_coeffHeckeU_comm.lean`
and
`P2M/Sol/S_ModularForm_coeffHeckeT_coeffHeckeU_comm.lean`
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
The `U`-type Hecke sum `ModularForm.heckeU`, the matrices
`ModularForm.heckeUpperMatrix` and `ModularForm.heckeDiagMatrix`, and their
basic lemmas are reused from existing files in this repository, where they are
definitionally the corresponding source carriers.
-/

module

public import MathlibExt.NumberTheory.ModularForms.TwoCuspReductionSpan

/-!
# Hecke operators on functions and on coefficient sequences

For a weight `k` and a natural number `p`, the `T`-type Hecke operator on
functions on the upper half-plane is
`heckeT k p f = heckeU k p f + f ∣[k] !![p, 0; 0, 1]`, where `heckeU k p f` is
the sum of the slashes of `f` by the matrices `!![1, j; 0, p]`, `0 ≤ j < p`.

On `q`-expansion coefficient sequences `a : ℕ → ℂ` the corresponding operators
are `coeffHeckeU p a n = a (n * p)` and
`coeffHeckeT k p a n = a (n * p) + [p ∣ n] p ^ (k - 1) a (n / p)`. Operators at
coprime indices commute.

## Main definitions

* `ModularForm.heckeT`: the `T`-type Hecke operator on functions.
* `ModularForm.coeffHeckeT`, `ModularForm.coeffHeckeU`: the Hecke operators on
  coefficient sequences.

## Main results

* `ModularForm.heckeU_apply`, `ModularForm.heckeT_apply`: explicit formulas.
* `ModularForm.coeffHeckeT_comm`, `ModularForm.coeffHeckeU_comm`,
  `ModularForm.coeffHeckeT_coeffHeckeU_comm`: commutation at coprime indices.
-/

@[expose] public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace ModularForm

/-- The denominator of `!![1, j; 0, p]` is `p`. -/
public theorem denom_heckeUpperMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : ℍ) :
    UpperHalfPlane.denom (heckeUpperMatrix p j) τ = p := by
  simp [UpperHalfPlane.denom, val_heckeUpperMatrix hp]

/-- The matrix `!![1, j; 0, p]` sends `τ` to `(τ + j) / p`. -/
public theorem coe_heckeUpperMatrix_smul {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : ℍ) :
    ((heckeUpperMatrix p j • τ : ℍ) : ℂ) = ((τ : ℂ) + j) / p := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_heckeUpperMatrix_pos p j)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_heckeUpperMatrix hp]

/-- The slash action by `!![1, j; 0, p]`. -/
public theorem slash_heckeUpperMatrix_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (j : ℕ)
    (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] heckeUpperMatrix p j) τ = (p : ℂ)⁻¹ * f (heckeUpperMatrix p j • τ) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [ModularForm.slash_apply, σ_heckeUpperMatrix, det_heckeUpperMatrix hp,
    denom_heckeUpperMatrix hp]
  simp only [ContinuousAlgEquiv.refl_apply, Nat.abs_cast, Complex.ofReal_natCast]
  rw [mul_assoc, ← zpow_add₀ hp', show k - 1 + -k = -1 by ring, zpow_neg_one, mul_comm]

/-- An explicit formula for the `U`-type Hecke sum. -/
public theorem heckeU_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (f : ℍ → ℂ) (τ : ℍ) :
    heckeU k p f τ = (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (heckeUpperMatrix p j • τ) := by
  simp only [heckeU, Finset.sum_apply, slash_heckeUpperMatrix_apply k hp, Finset.mul_sum]

/-- The `T`-type Hecke operator on functions on the upper half-plane: the
`U`-type sum plus the slash by `!![p, 0; 0, 1]`. -/
public def heckeT (k : ℤ) (p : ℕ) (f : ℍ → ℂ) : ℍ → ℂ :=
  heckeU k p f + f ∣[k] heckeDiagMatrix p

public theorem heckeT_eq_heckeU_add (k : ℤ) (p : ℕ) (f : ℍ → ℂ) :
    heckeT k p f = heckeU k p f + f ∣[k] heckeDiagMatrix p :=
  rfl

@[simp] public theorem heckeT_zero_left (k : ℤ) (f : ℍ → ℂ) : heckeT k 0 f = f := by
  simp [heckeT]

/-- An explicit formula for the `T`-type Hecke operator. -/
public theorem heckeT_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (f : ℍ → ℂ) (τ : ℍ) :
    heckeT k p f τ = (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (heckeUpperMatrix p j • τ)
      + (p : ℂ) ^ (k - 1) * f (heckeDiagMatrix p • τ) := by
  rw [heckeT, Pi.add_apply, heckeU_apply k hp, slash_heckeDiagMatrix_apply k hp]

@[simp] public theorem heckeT_zero (k : ℤ) (p : ℕ) : heckeT k p (0 : ℍ → ℂ) = 0 := by
  simp [heckeT]

public theorem heckeT_add (k : ℤ) (p : ℕ) (f g : ℍ → ℂ) :
    heckeT k p (f + g) = heckeT k p f + heckeT k p g := by
  simp only [heckeT, heckeU_add, SlashAction.add_slash]
  abel

public theorem heckeT_smul (k : ℤ) (p : ℕ) (c : ℂ) (f : ℍ → ℂ) :
    heckeT k p (c • f) = c • heckeT k p f := by
  rw [heckeT, heckeT, heckeU_smul, ModularForm.smul_slash, σ_heckeDiagMatrix,
    ContinuousAlgEquiv.refl_apply, smul_add]

/-- The `T`-type Hecke operator on `q`-expansion coefficient sequences. -/
public def coeffHeckeT (k : ℤ) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p) + if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0

/-- The `U`-type Hecke operator on `q`-expansion coefficient sequences. -/
public def coeffHeckeU (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p)

public theorem coeffHeckeT_apply (k : ℤ) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    coeffHeckeT k p a n = a (n * p) + if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0 :=
  rfl

public theorem coeffHeckeU_apply (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : coeffHeckeU p a n = a (n * p) :=
  rfl

public theorem coeffHeckeT_smul (k : ℤ) (p : ℕ) (c : ℂ) (a : ℕ → ℂ) :
    coeffHeckeT k p (c • a) = c • coeffHeckeT k p a := by
  funext n
  simp only [coeffHeckeT, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

public theorem coeffHeckeU_smul (p : ℕ) (c : ℂ) (a : ℕ → ℂ) :
    coeffHeckeU p (c • a) = c • coeffHeckeU p a :=
  rfl

/-- `U`-type coefficient operators commute. -/
public theorem coeffHeckeU_comm (p q : ℕ) (a : ℕ → ℂ) :
    coeffHeckeU p (coeffHeckeU q a) = coeffHeckeU q (coeffHeckeU p a) := by
  funext n
  simp only [coeffHeckeU_apply, Nat.mul_right_comm]

/-- `T`- and `U`-type coefficient operators at coprime indices commute. -/
public theorem coeffHeckeT_coeffHeckeU_comm (k : ℤ) {p q : ℕ} (hpq : Nat.Coprime p q)
    (a : ℕ → ℂ) :
    coeffHeckeT k p (coeffHeckeU q a) = coeffHeckeU q (coeffHeckeT k p a) := by
  funext n
  simp only [coeffHeckeT_apply, coeffHeckeU_apply]
  have hiff : p ∣ n * q ↔ p ∣ n := hpq.dvd_mul_right
  by_cases hpn : p ∣ n
  · rw [ite_eq_left hpn, ite_eq_left (hiff.mpr hpn), Nat.mul_right_comm, Nat.div_mul_right_comm hpn]
  · rw [ite_eq_right hpn, ite_eq_right (fun h => hpn (hiff.mp h)), Nat.mul_right_comm]

/-- `T`-type coefficient operators at coprime indices commute. -/
public theorem coeffHeckeT_comm (k : ℤ) {p q : ℕ} (hpq : Nat.Coprime p q) (a : ℕ → ℂ) :
    coeffHeckeT k p (coeffHeckeT k q a) = coeffHeckeT k q (coeffHeckeT k p a) := by
  funext n
  simp only [coeffHeckeT_apply]
  have hq : q ∣ n * p ↔ q ∣ n := hpq.symm.dvd_mul_right
  have hp : p ∣ n * q ↔ p ∣ n := hpq.dvd_mul_right
  have hpq' : ∀ {m : ℕ}, p ∣ m → (q ∣ m / p ↔ p * q ∣ m) := fun h =>
    Nat.dvd_div_iff_mul_dvd h
  have hqp' : ∀ {m : ℕ}, q ∣ m → (p ∣ m / q ↔ q * p ∣ m) := fun h =>
    Nat.dvd_div_iff_mul_dvd h
  by_cases hpn : p ∣ n <;> by_cases hqn : q ∣ n
  · have hpqn : p * q ∣ n := hpq.mul_dvd_of_dvd_of_dvd hpn hqn
    rw [ite_eq_left (hq.mpr hqn), ite_eq_left hpn, ite_eq_left ((hpq' hpn).mpr hpqn),
      ite_eq_left (hp.mpr hpn),
      ite_eq_left hqn, ite_eq_left ((hqp' hqn).mpr (mul_comm p q ▸ hpqn)),
      Nat.mul_right_comm, Nat.div_mul_right_comm hqn, Nat.div_mul_right_comm hpn,
      Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm q p]
    ring
  · have h1 : ¬ q ∣ n / p := fun h =>
      hqn (Nat.dvd_trans (Nat.dvd_mul_left q p) ((hpq' hpn).mp h))
    rw [ite_eq_right (fun h => hqn (hq.mp h)), ite_eq_left hpn, ite_eq_right h1,
      ite_eq_left (hp.mpr hpn), ite_eq_right hqn,
      Nat.mul_right_comm, Nat.div_mul_right_comm hpn]
    ring
  · have h1 : ¬ p ∣ n / q := fun h =>
      hpn (Nat.dvd_trans (Nat.dvd_mul_left p q) ((hqp' hqn).mp h))
    rw [ite_eq_left (hq.mpr hqn), ite_eq_right hpn, ite_eq_right (fun h => hpn (hp.mp h)),
      ite_eq_left hqn, ite_eq_right h1,
      Nat.mul_right_comm, Nat.div_mul_right_comm hqn]
    ring
  · rw [ite_eq_right (fun h => hqn (hq.mp h)), ite_eq_right hpn,
      ite_eq_right (fun h => hpn (hp.mp h)), ite_eq_right hqn,
      Nat.mul_right_comm]

end ModularForm

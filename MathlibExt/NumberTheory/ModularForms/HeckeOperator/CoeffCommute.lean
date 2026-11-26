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

public import MathlibExt.NumberTheory.ModularForms.HeckeOperator

/-!
# Commutation of the Hecke operators on coefficient sequences

The Hecke operators `ModularForm.coeffHeckeT` and `ModularForm.coeffHeckeU` on
`q`-expansion coefficient sequences, defined in
`MathlibExt.NumberTheory.ModularForms.HeckeOperator`, commute at coprime indices:
`coeffHeckeU p a n = a (n * p)` and
`coeffHeckeT k p a n = a (n * p) + [p ∣ n] p ^ (k - 1) a (n / p)`.

## Main results

* `ModularForm.coeffHeckeU_comm`: `U`-type operators commute.
* `ModularForm.coeffHeckeT_coeffHeckeU_comm`: `T p` and `U q` commute for coprime `p`, `q`.
* `ModularForm.coeffHeckeT_comm`: `T p` and `T q` commute for coprime `p`, `q`.
-/

@[expose] public section

namespace ModularForm

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

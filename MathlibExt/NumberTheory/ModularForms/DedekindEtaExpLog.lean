/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularForm_exp_logEta.lean`
and
`P2M/Sol/S_ModularForm_exp_logEta.lean`
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
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.NumberTheory.ModularForms.DedekindEta

@[expose] public section

open Complex

namespace ModularForm

private lemma summable_log_one_sub_eta_q (z : UpperHalfPlane) :
    Summable fun n : ℕ => Complex.log (1 - ModularForm.eta_q n (z : ℂ)) := by
  have h := Complex.summable_log_one_add_of_summable
    (Summable.of_norm (ModularForm.summable_eta_q z))
  simpa [sub_eq_add_neg] using h

/-- Exponentiating the chosen holomorphic logarithm series recovers the
Dedekind eta function: the exponential of
`π i z / 12 + ∑' n, log (1 - η_q n z)` is `η z` on the upper half-plane. -/
public theorem exp_logEta (z : UpperHalfPlane) :
    Complex.exp (Real.pi * Complex.I * (z : ℂ) / 12 +
      ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n (z : ℂ))) =
      ModularForm.eta z := by
  rw [Complex.exp_add, ModularForm.eta,
    ← Complex.cexp_tsum_eq_tprod
      (fun n => ModularForm.one_sub_eta_q_ne_zero n z.2) (summable_log_one_sub_eta_q z)]
  congr 1
  rw [Function.Periodic.qParam]
  congr 1
  push_cast
  ring

end ModularForm

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MvPolynomial_eq_of_forall_eval_rpow_eq.lean`
and
`P2M/Sol/S_MvPolynomial_eq_of_forall_eval_rpow_eq.lean`
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

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.Interval.Set.Infinite

@[expose] public section

namespace MvPolynomial

private theorem eq_of_forall_mem_forall_mem_eval_eq {K : Type*} [CommRing K] [IsDomain K]
    (P Q : MvPolynomial (Fin 2) K) (S T : Set K) (hS : S.Infinite) (hT : T.Infinite)
    (h : ∀ x ∈ S, ∀ y ∈ T, MvPolynomial.eval ![x, y] P = MvPolynomial.eval ![x, y] Q) :
    P = Q := by
  refine MvPolynomial.funext_set ![S, T] (fun i => by fin_cases i <;> simpa) ?_
  intro v hv
  have h0 : v 0 ∈ S := by simpa using hv 0 (Set.mem_univ _)
  have h1 : v 1 ∈ T := by simpa using hv 1 (Set.mem_univ _)
  have hv' : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv']; exact h _ h0 _ h1

/-- Equality of bivariate complex polynomials from infinitely many fibers
along real powers `N ^ u`.

If two polynomials in two complex variables agree at `(x, N ^ u)` for every
`x` in an infinite set and every real `u > u₀`, where `N > 1`, then the
polynomials are equal. The second coordinates `N ^ u` for `u > u₀` form an
infinite set because `u ↦ N ^ u` is strictly monotone, so the usual
two-variable polynomial identity principle applies. -/
public theorem eq_of_forall_eval_rpow_eq (N : ℕ) (hN : 1 < N) (u₀ : ℝ) (S : Set ℂ)
    (hS : S.Infinite) (P Q : MvPolynomial (Fin 2) ℂ)
    (h : ∀ x ∈ S, ∀ u : ℝ, u₀ < u →
      MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] P =
        MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] Q) :
    P = Q := by
  have hN' : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set f : ℝ → ℂ := fun u => (((N : ℝ) ^ u : ℝ) : ℂ) with hf
  have hfinj : Function.Injective f := by
    intro a b hab
    have h1 : (N : ℝ) ^ a = (N : ℝ) ^ b := by
      simpa [hf] using hab
    exact (Real.strictMono_rpow_of_base_gt_one hN').injective h1
  have hT : (f '' Set.Ioi u₀).Infinite := (Set.Ioi_infinite u₀).image hfinj.injOn
  refine eq_of_forall_mem_forall_mem_eval_eq P Q S (f '' Set.Ioi u₀) hS hT ?_
  rintro x hx _ ⟨u, hu, rfl⟩
  exact h x hx u hu

end MvPolynomial

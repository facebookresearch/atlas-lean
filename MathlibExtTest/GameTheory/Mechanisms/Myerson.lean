/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.Mechanisms.Myerson
import Mathlib.Tactic.Linarith

/-- Boundary check: in any DSIC auction, bidder `0`'s allocation at
own bid `1` is at most their allocation at own bid `3`, with nonnegative
other bids. -/
example {x : (Fin 2 → ℝ) → Fin 2 → ℝ} {pay : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (h : DSIC x pay) (bminus : Fin 2 → ℝ) (hbminus : ∀ j, 0 ≤ bminus j) :
    x (Function.update bminus 0 1) 0 ≤ x (Function.update bminus 0 3) 0 :=
  myerson_monotone h 0 bminus hbminus (by norm_num) (by norm_num) (by norm_num)

/-- Equal bids give equal allocations (the trivial boundary of
monotonicity in both directions is not asserted; this checks the
statement at `z = z'`). -/
example {x : (Fin 2 → ℝ) → Fin 2 → ℝ} {pay : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (h : DSIC x pay) (bminus : Fin 2 → ℝ) (hbminus : ∀ j, 0 ≤ bminus j)
    (z : ℝ) (hz : 0 ≤ z) :
    x (Function.update bminus 0 z) 0 ≤ x (Function.update bminus 0 z) 0 :=
  myerson_monotone h 0 bminus hbminus hz hz le_rfl

/-- A posted-price allocation at price `1`, with independent goods for two bidders. -/
private noncomputable def postedAllocation (b : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  if 1 ≤ b i then 1 else 0

/-- Charge the posted price on the valid domain; subsidize invalid negative reports. -/
private noncomputable def postedPayment (b : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  if b i < 0 then -1 else postedAllocation b i

/-- Truthfulness is insensitive to the deliberately bad extension at negative reports. -/
private lemma posted_dsic : DSIC postedAllocation postedPayment := by
  intro i vi bi bminus hvi hbi _
  by_cases hv : 1 ≤ vi <;> by_cases hb : 1 ≤ bi <;>
    simp [postedPayment, postedAllocation, hv, hb, not_lt.mpr hvi, not_lt.mpr hbi]
  linarith

/-- The nonconstant posted-price mechanism exercises the monotonicity theorem. -/
example : postedAllocation (Function.update (fun _ => 0) 0 (1 / 2)) 0 ≤
    postedAllocation (Function.update (fun _ => 0) 0 2) 0 :=
  myerson_monotone posted_dsic 0 (fun _ => 0) (fun _ => le_rfl)
    (by norm_num) (by norm_num) (by norm_num)

/-- Negative reports are invalid: allowing one would make the subsidy a profitable lie. -/
example :
    0 * postedAllocation (Function.update (fun _ => 0) 0 0) 0 -
        postedPayment (Function.update (fun _ => 0) 0 0) 0 <
      0 * postedAllocation (Function.update (fun _ => 0) 0 (-1)) 0 -
        postedPayment (Function.update (fun _ => 0) 0 (-1)) 0 := by
  norm_num [postedPayment, postedAllocation]

/-- Removing the posted payment is not DSIC, even with only valid nonnegative bids. -/
example : ¬ DSIC postedAllocation (fun _ _ => 0) := by
  intro h
  have bad := h 0 (1 / 2) 1 (fun _ => 0) (by norm_num) (by norm_num) (fun _ => le_rfl)
  norm_num [postedAllocation] at bad

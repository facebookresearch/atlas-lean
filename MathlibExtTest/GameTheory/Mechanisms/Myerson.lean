/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.Mechanisms.Myerson

/-- Boundary check: in any DSIC auction, bidder `0`'s allocation at
own bid `1` is at most their allocation at own bid `3`, whatever the
other bids are. -/
example {x : (Fin 2 → ℝ) → Fin 2 → ℝ} {pay : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (h : DSIC x pay) (bminus : Fin 2 → ℝ) :
    x (Function.update bminus 0 1) 0 ≤ x (Function.update bminus 0 3) 0 :=
  myerson_monotone h 0 bminus (by norm_num) (by norm_num) (by norm_num)

/-- Equal bids give equal allocations (the trivial boundary of
monotonicity in both directions is not asserted; this checks the
statement at `z = z'`). -/
example {x : (Fin 2 → ℝ) → Fin 2 → ℝ} {pay : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (h : DSIC x pay) (bminus : Fin 2 → ℝ) (z : ℝ) (hz : 0 ≤ z) :
    x (Function.update bminus 0 z) 0 ≤ x (Function.update bminus 0 z) 0 :=
  myerson_monotone h 0 bminus hz hz le_rfl

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QAnalogCollatz

/-! # Parity of perturbed q-Collatz iterates -/

namespace MetaMathlibExt

@[expose] public section

open PowerSeries

/-- **A perturbation at $q^n$ flips the parity of the $n$-th iterate.** Let
$A, B, U, V \in \mathbb{F}_2[[q]]$ with $A$, $B$ and $V$ odd (constant term $1$), let $T_{A,B}$ be
the $q$-analog of the $3x+1$ map, and let $n \ge 0$ be an integer. Then the $n$-th iterates
$T_{A,B}^n(U + q^n V)$ and $T_{A,B}^n(U)$ have different constant terms.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Corollary 9 (`jis-2025-25.6.8-cor-9`). -/
public theorem qCollatz_iterate_parity_flip (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) (n : ℕ) (U V : PowerSeries (ZMod 2))
    (hV : constantCoeff V ≠ 0) :
    constantCoeff ((qCollatz A B)^[n] (U + X ^ n * V)) ≠
      constantCoeff ((qCollatz A B)^[n] U) := by
  cases n with
  | zero =>
    simpa only [Function.iterate_zero_apply, pow_zero, one_mul, map_add, ne_eq, add_eq_left]
      using hV
  | succ n =>
    obtain ⟨W, hW, heq⟩ := qCollatz_iterate_add_X_pow_mul A B hA hB n U V hV (n + 1) le_rfl
    rw [heq, Nat.sub_self, pow_zero, one_mul, map_add]
    simpa only [ne_eq, add_eq_left] using hW

end

end MetaMathlibExt

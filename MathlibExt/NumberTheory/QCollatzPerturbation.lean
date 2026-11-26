/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QAnalogCollatz

/-! # One-step perturbations of the q-Collatz map -/

namespace MetaMathlibExt

@[expose] public section

open PowerSeries

/-- **A perturbation at $q^{n+1}$ moves to $q^n$ under $T_{A,B}$.** Let $A, B, U, V$ be power
series in $\mathbb{F}_2[[q]]$ with $A$, $B$ and $V$ odd (constant term $1$), let $T_{A,B}$ be the
$q$-analog of the $3x+1$ map, and let $n \ge 0$ be an integer. Then there is an odd power series
$W \in \mathbb{F}_2[[q]]$ with $T_{A,B}(U + q^{n+1} V) = T_{A,B}(U) + q^n W$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Lemma 7 (`jis-2025-25.6.8-lem-7`). -/
public theorem qCollatz_add_X_pow_mul (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) (n : ℕ) (U V : PowerSeries (ZMod 2))
    (hV : constantCoeff V ≠ 0) :
    ∃ W : PowerSeries (ZMod 2), constantCoeff W ≠ 0 ∧
      qCollatz A B (U + X ^ (n + 1) * V) = qCollatz A B U + X ^ n * W := by
  simpa only [Function.iterate_one, Nat.add_sub_cancel] using
    qCollatz_iterate_add_X_pow_mul A B hA hB n U V hV 1 (Nat.succ_le_succ (Nat.zero_le n))

end

end MetaMathlibExt

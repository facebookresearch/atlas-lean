/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Tactic.LinearCombination

/-!
# Powers of a root of the Lucas characteristic polynomial
-/

namespace MetaMathlibExt

/-- **Powers of a root of the Lucas characteristic polynomial.** Let $x$ and $y \neq 0$ be
integers and let $(U_n)$ be the Lucas sequence with parameters $(x, y)$, given by $U_0 = 0$,
$U_1 = 1$ and $U_{n+2} = x U_{n+1} - y U_n$. If $\alpha$ is a complex number with
$\alpha^2 - x\alpha + y = 0$, then $\alpha^n = \alpha U_n - y U_{n-1}$ for every $n \geq 1$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.1 (i), (ii) (`fq-2024-earplynch07182024-lem-2.1`). -/
public theorem lucasU_root_pow (P : LucasSequenceParams) {α : ℂ}
    (hα : α ^ 2 - P.p * α + P.q = 0) {n : ℕ} (hn : 1 ≤ n) :
    α ^ n = α * lucasU P n - P.q * lucasU P (n - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  clear hn
  simp only [Nat.succ_sub_one]
  induction n with
  | zero => simp [lucasU]
  | succ n ih =>
    rw [pow_succ α (n + 1), ih, lucasU_add_two]
    push_cast
    linear_combination (lucasU P (n + 1) : ℂ) * hα

end MetaMathlibExt

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Tactic.Ring

/-!
# Shift congruence for the Lucas recurrence

If `m` divides the Lucas term `U_t`, shifting any solution of the same recurrence by `t`
multiplies it by `U_{t+1}` modulo `m`.
-/

namespace MetaMathlibExt

-- The integral shift identity holds independently of the source's coprimality hypothesis.
set_option linter.unusedVariables false in
/-- **Shift congruence for the Lucas recurrence.** Let $U = U(P, Q)$ be the Lucas sequence with
integer parameters $P$ and $Q \ne 0$, and let $(W_n)_{n \ge 0}$ be a sequence of integers with
$W_{n+2} = P W_{n+1} - Q W_n$ for every $n \ge 0$. If $t \ge 0$ and $m$ are integers with
$m \mid U_t$ and $\gcd(m, Q) = 1$, then $W_{n+t} \equiv U_{t+1} W_n \pmod{m}$ for every $n \ge 0$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Lemma 2.5 (`integers-2025-A107-lem-2-5`). -/
public theorem lucas_recurrence_add_modEq_of_dvd_lucasU
    (L : LucasSequenceParams) (W : ℕ → ℤ)
    (hW : ∀ n, W (n + 2) = L.p * W (n + 1) - L.q * W n)
    (t : ℕ) (m : ℤ) (ht : m ∣ lucasU L t) (hm : Int.gcd m L.q = 1) (n : ℕ) :
    W (n + t) ≡ lucasU L (t + 1) * W n [ZMOD m] := by
  have shift (k j : ℕ) : W (j + k) = lucasU L (k + 1) * W j +
      lucasU L k * (W (j + 1) - L.p * W j) := by
    induction k generalizing j with
    | zero => simp [lucasU]
    | succ k ih =>
      rw [show j + (k + 1) = (j + 1) + k by omega, ih (j + 1), hW j, lucasU_add_two L k]
      ring
  rw [shift t n, Int.add_modEq_left_iff]
  exact dvd_mul_of_dvd_left ht _

end MetaMathlibExt

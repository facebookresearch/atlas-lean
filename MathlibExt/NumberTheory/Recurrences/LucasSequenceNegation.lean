/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Tactic.Ring

/-! # Sign changes of Lucas sequences under negation of the first parameter -/

namespace MetaMathlibExt

/-- **Lucas sequences under negation of the first parameter.** For integers $P$ and $Q \ne 0$ and
every natural number $n$, the Lucas sequences $U$ and $V$ satisfy
$U_n(-P, Q) = (-1)^{n+1} U_n(P, Q)$ and $V_n(-P, Q) = (-1)^n V_n(P, Q)$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Proposition 2.3 (vii), (viii)
(`integers-2025-A107-prop-2-3`). -/
public theorem lucasU_lucasV_neg_p
    (L : LucasSequenceParams) (n : ℕ) :
    lucasU ⟨-L.p, L.q, L.q_ne_zero⟩ n = (-1) ^ (n + 1) * lucasU L n ∧
      lucasV ⟨-L.p, L.q, L.q_ne_zero⟩ n = (-1) ^ n * lucasV L n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [lucasU, lucasV]
  | one => simp [lucasU, lucasV]
  | more n ih₀ ih₁ =>
    constructor
    · rw [lucasU_add_two, lucasU_add_two, ih₀.1, ih₁.1]
      simp only [pow_add]
      ring
    · rw [lucasV, lucasV, ih₀.2, ih₁.2]
      simp only [pow_add]
      ring

end MetaMathlibExt

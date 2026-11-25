/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Subsequences of a second-order linear recurrence

For Lucas sequence parameters `(P, Q)` and an integer sequence `w` with
`w (n + 2) = P * w (n + 1) - Q * w n`, the main result `subsequence_secondOrderRecurrence` shows
that for `t > 0` the subsequence `n ↦ w (t * n + r)` satisfies the second-order recurrence with
coefficients `V_t` and `Q ^ t`, where `U` and `V` are the Lucas sequences of `(P, Q)`, and that its
discriminant is `V_t ^ 2 - 4 * Q ^ t = U_t ^ 2 * (P ^ 2 - 4 * Q)`.

The recurrence is proved in the form `w (n + 2 * t) + Q ^ t * w n = V_t * w (n + t)` by two-step
induction on `t`, and the discriminant identity follows from `V_t = 2 * U_(t+1) - P * U_t` and
Cassini's identity for `U`.
-/

namespace MetaMathlibExt

/-- The shifted recurrence: for every `t` and `n`, `w (n + 2t) + Q^t w n = V_t w (n + t)`. -/
private theorem subsequence_secondOrderRecurrence_add_two_mul
    (params : LucasSequenceParams) (w : ℕ → ℤ)
    (hw : ∀ n : ℕ, w (n + 2) = params.p * w (n + 1) - params.q * w n) (t : ℕ) :
    ∀ n : ℕ, w (n + 2 * t) + params.q ^ t * w n = lucasV params t * w (n + t) := by
  induction t using Nat.twoStepInduction with
  | zero =>
    intro n
    simp only [Nat.mul_zero, Nat.add_zero, pow_zero, lucasV]
    ring
  | one =>
    intro n
    simp only [Nat.mul_one, pow_one, lucasV]
    linear_combination hw n
  | more t ih0 ih1 =>
    intro n
    have h1 : w (n + 2 * t + 3) + params.q ^ (t + 1) * w (n + 1) =
        lucasV params (t + 1) * w (n + t + 2) := by
      have h := ih1 (n + 1)
      rwa [show n + 1 + 2 * (t + 1) = n + 2 * t + 3 by ring,
        show n + 1 + (t + 1) = n + t + 2 by ring] at h
    have h0 : w (n + 2 * t + 2) + params.q ^ t * w (n + 2) =
        lucasV params t * w (n + t + 2) := by
      have h := ih0 (n + 2)
      rwa [show n + 2 + 2 * t = n + 2 * t + 2 by ring,
        show n + 2 + t = n + t + 2 by ring] at h
    have hA : w (n + 2 * t + 4) =
        params.p * w (n + 2 * t + 3) - params.q * w (n + 2 * t + 2) := hw (n + 2 * t + 2)
    have hB := hw n
    have hV : lucasV params (t + 2) =
        params.p * lucasV params (t + 1) - params.q * lucasV params t := rfl
    rw [show n + 2 * (t + 2) = n + 2 * t + 4 by ring, show n + (t + 2) = n + t + 2 by ring, hV]
    linear_combination hA + params.p * h1 - params.q * h0 + params.q ^ (t + 1) * hB

/-- The companion sequence in terms of the first: `V_n = 2 U_(n+1) - P U_n`. -/
private theorem subsequence_secondOrderRecurrence_lucasV_eq
    (params : LucasSequenceParams) (n : ℕ) :
    lucasV params n = 2 * lucasU params (n + 1) - params.p * lucasU params n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [lucasV, lucasU]
  | one =>
    simp only [lucasV, lucasU]
    ring
  | more n ih0 ih1 =>
    have ih1' : lucasV params (n + 1) =
        2 * lucasU params (n + 2) - params.p * lucasU params (n + 1) := ih1
    have hV : lucasV params (n + 2) =
        params.p * lucasV params (n + 1) - params.q * lucasV params n := rfl
    have hU3 : lucasU params (n + 3) =
        params.p * lucasU params (n + 2) - params.q * lucasU params (n + 1) := rfl
    have hU2 : lucasU params (n + 2) =
        params.p * lucasU params (n + 1) - params.q * lucasU params n := rfl
    change lucasV params (n + 2) = 2 * lucasU params (n + 3) - params.p * lucasU params (n + 2)
    linear_combination hV + params.p * ih1' - params.q * ih0 - 2 * hU3 + params.p * hU2

-- Both identities also hold for `t = 0`; the hypothesis `ht` is kept from the source's statement.
set_option linter.unusedVariables false in
/-- **Subsequences of a second-order linear recurrence.** Let $(P, Q)$ be Lucas sequence
parameters (integers with $Q \ne 0$), let $U_n$ and $V_n$ be the terms of the Lucas sequence
$U(P, Q)$ and of the companion Lucas sequence $V(P, Q)$, and let $(w_n)_{n \ge 0}$ be an integer
sequence with $w_{n+2} = P w_{n+1} - Q w_n$ for every natural number $n$. Then for all natural
numbers $t > 0$ and $r$, the subsequence $w'_n = w_{tn + r}$ satisfies
$w'_{n+2} = V_t w'_{n+1} - Q^t w'_n$ for every natural number $n$, and
$V_t^2 - 4 Q^t = U_t^2 (P^2 - 4Q)$.

The source writes the recurrence as $w_{n+2} = a w_{n+1} + b w_n$,
with subsequence coefficients $a' = V_t$ and $b' = (-1)^{t+1} b^t$ and discriminant
$D(a, b) = a^2 + 4b$; this is the statement above with $P = a$ and $Q = -b$. The source's
identification of the characteristic roots of the new recurrence as $\alpha^t$ and $\beta^t$ is
not part of this statement.

Source: Somer and Křížek, *Generalization of a Theorem of Vélez on
Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS
25 (2025), Article A1, Theorem 2.4 (`integers-2025-A1-thm-2-4`). -/
public theorem subsequence_secondOrderRecurrence
    (params : LucasSequenceParams) (w : ℕ → ℤ)
    (hw : ∀ n : ℕ, w (n + 2) = params.p * w (n + 1) - params.q * w n)
    (t r : ℕ) (ht : 0 < t) :
    (∀ n : ℕ, w (t * (n + 2) + r)
      = lucasV params t * w (t * (n + 1) + r)
        - params.q ^ t * w (t * n + r)) ∧
    (lucasV params t) ^ 2 - 4 * params.q ^ t
      = (lucasU params t) ^ 2 * (params.p ^ 2 - 4 * params.q) := by
  refine ⟨fun n => ?_, ?_⟩
  · have h := subsequence_secondOrderRecurrence_add_two_mul params w hw t (t * n + r)
    rw [show t * n + r + 2 * t = t * (n + 2) + r by ring,
      show t * n + r + t = t * (n + 1) + r by ring] at h
    linear_combination h
  · have hV := subsequence_secondOrderRecurrence_lucasV_eq params t
    have hC := lucasU_cassini params t
    have hU : lucasU params (t + 2) =
        params.p * lucasU params (t + 1) - params.q * lucasU params t := rfl
    linear_combination
      (lucasV params t + 2 * lucasU params (t + 1) - params.p * lucasU params t) * hV +
        4 * hC + 4 * lucasU params t * hU

end MetaMathlibExt
